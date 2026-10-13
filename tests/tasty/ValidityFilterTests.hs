{-# LANGUAGE OverloadedStrings #-}

module ValidityFilterTests (tests) where

import Control.Exception (bracket, try)
import qualified Control.Monad.State as Lazy
import Control.Monad.State.Strict (evalStateT)
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as B
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.List (isInfixOf)
import qualified Data.Text as T
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Solver.Monad as SM
import qualified Language.Fixpoint.Solver.Stats as Stats
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import qualified SMTLIB.Backends as Backend
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests = testGroup "validity filtering" [solverTests, scriptedTests, checkErrorTests, parserTests]

-- filterValid p qs = [x | (q, x) <- qs, p => q is proved]: one check per
-- candidate, input order and duplicate payloads preserved.
solverTests :: TestTree
solverTests =
    testGroup
        "actual solvers"
        [ testGroup
            (show solver)
            [ testCase "each invalid candidate is refuted by its own check" $ do
                (accepted, counters) <- withSolver solver environment $ do
                    result <- SM.filterValid F.dummySpan [] nonnegative [(F.PAtom F.Lt x (integer (-n)), n) | n <- [1 .. 256]]
                    (,) result <$> SM.stats
                accepted @?= []
                Stats.numChck counters @?= 256
            , testCase "valid candidates are admitted in order" $ do
                let candidates = [(F.PAtom F.Ge x (integer (-n)), n `mod` 7) | n <- [0 .. 255]]
                (accepted, counters) <- withSolver solver environment $ do
                    result <- SM.filterValid F.dummySpan [] nonnegative candidates
                    (,) result <$> SM.stats
                accepted @?= map snd candidates
                Stats.numChck counters @?= 256
                Stats.numVald counters @?= 256
            , testCase "an empty group needs no solver check" $ do
                (accepted, counters) <- withSolver solver environment $ do
                    result <- SM.filterValid F.dummySpan [] nonnegative ([] :: [(F.Expr, Int)])
                    (,) result <$> SM.stats
                accepted @?= []
                Stats.numChck counters @?= 0
            , testCase "mixed results preserve order, duplicate payloads, and scoped definitions" $ do
                let predicates = [(F.PAtom F.Ge x (integer 0), 4), (F.PAtom F.Gt x (integer 0), 9), (F.PTrue, 4), (F.PFalse, 7), (F.EVar "defined", 2)]
                    definitions = [F.Equ "defined" [] F.PTrue F.boolSort False]
                actual <- withSolver solver environment (SM.filterValid F.dummySpan definitions nonnegative predicates)
                actual @?= [4, 4, 2]
            , testCase "quantified candidates are proved or retained individually" $ do
                let identity = F.PAll [("y", F.intSort)] (F.PAtom F.Eq (F.EVar "y") (F.EVar "y"))
                    impossible = F.PAll [("y", F.intSort)] (F.PAtom F.Ge (F.EVar "y") x)
                actual <- withSolver solver environment (SM.filterValid F.dummySpan [] F.PTrue [(identity, 0), (impossible, 1), (F.PFalse, 2)])
                actual @?= [0]
            , testCase "inconsistent premises prove every member" $ do
                (accepted, counters) <- withSolver solver environment $ do
                    result <- SM.filterValid F.dummySpan [] F.PFalse [(F.PFalse, 1 :: Int), (F.PTrue, 1)]
                    (,) result <$> SM.stats
                accepted @?= [1, 1]
                Stats.numChck counters @?= 2
            ]
        | solver <- [Config.Z3, Config.Cvc5]
        ]

-- A reply decides only its own member: UNSAT admits it, SAT and UNKNOWN omit
-- it, and no reply is consulted for another member. No model is requested.
scriptedTests :: TestTree
scriptedTests =
    testGroup
        "check-sat replies decide only their own member"
        [ testCase label $ withContext $ \context -> do
            checks <- newIORef replies
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = fail "validity filtering requested a model"
                    | otherwise = atomicModifyIORef' checks $ \remaining -> case remaining of
                        response : rest -> (rest, response)
                        [] -> error "more check-sat commands than candidates"
            solver <- fakeSolver send
            (accepted, counters) <- runFilter context{SMT.ctxSolver = solver} environment $ do
                result <- SM.filterValid F.dummySpan [] F.PTrue candidates
                (,) result <$> SM.stats
            accepted @?= expected
            Stats.numChck counters @?= length candidates
            readIORef checks >>= (@?= [])
        | (label, replies, candidates, expected) <-
            [ ("UNKNOWN omits only its member", ["unknown", "unsat"], [(F.PFalse, 1 :: Int), (F.PTrue, 0)], [0])
            , ("SAT omits only its member", ["sat", "unsat"], [(F.PFalse, 1), (F.PTrue, 0)], [0])
            , ("later replies do not revoke an admitted member", ["unsat", "unknown", "sat", "unsat"], [(F.PTrue, 4), (F.PFalse, 7), (F.PFalse, 7), (F.PTrue, 4)], [4, 4])
            ]
        ]

checkErrorTests :: TestTree
checkErrorTests =
    testGroup
        "check-sat errors remain fatal"
        [ testCase label $ withContext $ \context -> do
            requests <- newIORef (0 :: Int)
            let send _ = do
                    atomicModifyIORef' requests (\count -> (count + 1, ()))
                    pure response
            solver <- fakeSolver send
            outcome <- try (runFilter context{SMT.ctxSolver = solver} environment (SM.filterValid F.dummySpan [] F.PTrue [(F.PTrue, 0 :: Int)])) :: IO (Either F.Error [Int])
            case outcome of
                Left failure -> assertBool "original check-sat diagnostic was lost" (any (isInfixOf "crash: SMTLIB2 respSat = Error" . show . F.errMsg) (F.errs failure))
                Right _ -> assertFailure "check-sat error was treated as an incomplete proof"
            readIORef requests >>= (@?= 1)
        | (label, response) <- [("error response", "(error \"check-sat failed\")"), ("bare unsupported response", "unsupported")]
        ]

parserTests :: TestTree
parserTests =
    testGroup
        "opaque model values"
        [ testCase "nested expressions, quoted symbols, strings, and negative numerals are preserved" $ withContext $ \context -> do
            let values = ["(forall ((|y (quoted)| Int)) (>= |y (quoted)| 0))", "(ite true \"a)\"\"b\" \"(c\")", "(- 3)", "|false|", "\"false\""]
                names = ["first", "second", "third", "fourth", "fifth"]
                response = B.pack ("(" ++ concat ["(" ++ T.unpack (F.symbolSmtText name) ++ " " ++ T.unpack value ++ ")" | (name, value) <- zip names values] ++ ")")
            solver <- fakeSolver (const (pure response))
            actual <- Lazy.evalStateT (SMT.command (SMT.GetValue names)) context{SMT.ctxSolver = solver}
            actual @?= SMT.Values (zip names values)
        ]

withSolver :: Config.SMTSolver -> F.SymEnv -> SM.SolveM () a -> IO a
withSolver solver env action = bracket (SMT.makeContextNoLog cfg) SMT.cleanupContext $ \context ->
    runFilter context env (SM.liftSMT (SMT.smtDecls [("x", F.intSort)]) >> action)
  where
    cfg = Config.defConfig{Config.solver = solver}

withContext :: (SMT.Context -> IO a) -> IO a
withContext = bracket (SMT.makeContextNoLog Config.defConfig) SMT.cleanupContext

-- NoQueuing requires acknowledgments for initialization and ordinary commands.
-- Only actual query commands consume the scripted observations. Unexpected
-- command kinds fail, and source formation/serialization still runs normally.
fakeSolver :: (Builder -> IO B.ByteString) -> IO Backend.Solver
fakeSolver observe = Backend.initSolver Backend.NoQueuing (Backend.Backend send (const (pure ())))
  where
    send bytes
        | command == "(check-sat)" || "(get-value " `T.isPrefixOf` command = observe bytes
        | any (`T.isPrefixOf` command) ["(set-option ", "(push ", "(pop ", "(declare-fun ", "(define-fun ", "(assert ", ";"] = pure "success"
        | otherwise = fail ("unexpected scripted SMT command: " ++ T.unpack command)
      where
        command = T.strip (render bytes)

runFilter :: SMT.Context -> F.SymEnv -> SM.SolveM () a -> IO a
runFilter context env action = evalStateT action (SM.SS context{SMT.ctxSymEnv = env} mempty (C.ElabParam (Config.solverFlags (SMT.config context)) "validity filtering" env))

environment :: F.SymEnv
environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("x", F.intSort)]}

x, nonnegative :: F.Expr
x = F.EVar "x"
nonnegative = F.PAtom F.Ge x (integer 0)

integer :: Int -> F.Expr
integer = F.ECon . F.I . fromIntegral

render :: Builder -> T.Text
render = T.pack . B.unpack . toLazyByteString
