{-# LANGUAGE OverloadedStrings #-}

module ModelFilterTests (tests) where

import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad (filterM, forM_)
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
tests = testGroup "model-guided validity filtering" [solverTests, pointwiseModelTests, incompleteTests, checkErrorTests, parserTests]

solverTests :: TestTree
solverTests =
    testGroup
        "actual solver models"
        [ testGroup
            (show solver)
            [ testCase "a model eliminates 256 invalid predicates in one check" $ do
                (accepted, counters) <- withSolver solver environment $ do
                    result <- SM.filterValid F.dummySpan [] nonnegative [(F.PAtom F.Lt x (integer (-n)), n) | n <- [1 .. 256]]
                    (,) result <$> SM.stats
                accepted @?= []
                Stats.numChck counters @?= 1
            , testCase "pointwise proofs admit 256 ordered valid payloads" $ do
                let candidates = [(F.PAtom F.Ge x (integer (-n)), n `mod` 7) | n <- [0 .. 255]]
                (accepted, counters) <- withSolver solver environment $ do
                    result <- SM.filterValid F.dummySpan [] nonnegative candidates
                    (,) result <$> SM.stats
                accepted @?= map snd candidates
                Stats.numChck counters @?= 256
                Stats.numVald counters @?= 256
            , testCase "an empty group needs no solver observation" $ do
                (accepted, counters) <- withSolver solver environment $ do
                    result <- SM.filterValid F.dummySpan [] nonnegative ([] :: [(F.Expr, Int)])
                    (,) result <$> SM.stats
                accepted @?= []
                Stats.numChck counters @?= 0
            , testCase "mixed results preserve order, duplicate payloads, and scoped definitions" $ do
                let predicates = [(F.PAtom F.Ge x (integer 0), 4), (F.PAtom F.Gt x (integer 0), 9), (F.PTrue, 4), (F.PFalse, 7), (F.EVar "defined", 2)]
                    definitions = [F.Equ "defined" [] F.PTrue F.boolSort False]
                actual <- withSolver solver environment (SM.filterValid F.dummySpan definitions nonnegative predicates)
                reference <- withSolver solver environment (pointwise definitions nonnegative predicates)
                actual @?= [4, 4, 2]
                actual @?= reference
            , testCase "source, theory, literal, and definition names cannot capture observers" $ do
                let source = candidateName 0
                    native = candidateName 1
                    literal = candidateName 2
                    defined = candidateName 3
                    nativeWire = F.symbolSmtText native
                    literalWire = F.symbolSmtText literal
                    declarations = [(source, F.boolSort)]
                    decorated =
                        environment
                            { F.seSort = F.fromListSEnv declarations <> F.seSort environment
                            , F.seTheory = F.fromListSEnv [("native_alias", F.Thy "native_alias" nativeWire F.boolSort F.Theory)]
                            }
                    predicates = [(F.EVar source, 0), (F.EVar "native_alias", 1), (F.ECon (F.L literalWire F.boolSort), 2), (F.EVar defined, 3), (F.PFalse, 4)]
                actual <- withSolver solver decorated $ do
                    SM.liftSMT $ do
                        SMT.smtDecls declarations
                        SMT.smtFuncDecl nativeWire ([], F.SBool)
                        SMT.smtFuncDecl literalWire ([], F.SBool)
                    SM.filterValid
                        F.dummySpan
                        [F.Equ defined [] F.PTrue F.boolSort False]
                        (F.PAnd (map fst (take 3 predicates)))
                        predicates
                actual @?= [0, 1, 2, 3]
            , testCase "quantified predicates remain candidates when model values are opaque" $ do
                let identity = F.PAll [("y", F.intSort)] (F.PAtom F.Eq (F.EVar "y") (F.EVar "y"))
                    impossible = F.PAll [("y", F.intSort)] (F.PAtom F.Ge (F.EVar "y") x)
                actual <- withSolver solver environment (SM.filterValid F.dummySpan [] F.PTrue [(identity, 0), (impossible, 1), (F.PFalse, 2)])
                reference <- withSolver solver environment (pointwise [] F.PTrue [(identity, 0), (impossible, 1), (F.PFalse, 2)])
                actual @?= [0]
                actual @?= reference
            ]
        | solver <- [Config.Z3, Config.Cvc5]
        ]

pointwiseModelTests :: TestTree
pointwiseModelTests =
    testGroup
        "pointwise proofs with shared countermodels"
        [ testCase "Z3 one countermodel eliminates 1557 false candidates" $ do
            (accepted, counters) <- withSolver Config.Z3 environment $ do
                result <- SM.filterValid F.dummySpan [] (F.PAtom F.Eq x (integer 0)) [(F.PAtom F.Gt x (integer n), n) | n <- [0 .. 1556]]
                (,) result <$> SM.stats
            accepted @?= []
            Stats.numChck counters @?= 1
        , testCase "Z3 inconsistent premises prove every member" $ do
            (accepted, counters) <- withSolver Config.Z3 environment $ do
                result <- SM.filterValid F.dummySpan [] F.PFalse [(F.PFalse, 1 :: Int), (F.PTrue, 1)]
                (,) result <$> SM.stats
            accepted @?= [1, 1]
            Stats.numChck counters @?= 2
        , testCase "Z3 local countermodel retains valid members in original order" $ do
            let candidates = [(F.PFalse, 0 :: Int), (F.PTrue, 1), (F.PFalse, 2)]
            actual <- withSolver Config.Z3 environment (SM.filterValid F.dummySpan [] F.PTrue candidates)
            reference <- withSolver Config.Z3 environment (pointwise [] F.PTrue candidates)
            actual @?= [1]
            actual @?= reference
        , testCase "only individual SAT refutes the first member when models are unsupported" $ withContext $ \context -> do
            checks <- newIORef (["sat", "unsat"] :: [B.ByteString])
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = pure "unsupported"
                    | otherwise = atomicModifyIORef' checks $ \remaining -> case remaining of
                        response : rest -> (rest, response)
                        [] -> error "unexpected check-sat in local witness test"
            solver <- fakeSolver send
            (accepted, counters) <- runFilter context{SMT.ctxSolver = solver} environment $ do
                result <- SM.filterValid F.dummySpan [] F.PTrue [(F.PFalse, 1 :: Int), (F.PTrue, 0)]
                (,) result <$> SM.stats
            accepted @?= [0]
            Stats.numChck counters @?= 2
            readIORef checks >>= (@?= [])
        , testCase "opaque model values leave other members to their independent proofs" $ withContext $ \context -> do
            checks <- newIORef (["sat", "unsat", "sat"] :: [B.ByteString])
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = do
                        let names = drop 1 (T.words (T.map (\c -> if c == '(' || c == ')' then ' ' else c) (render bytes)))
                            value name = if name == F.symbolSmtText (candidateName 1) then "(ite true true false)" else "(ite true false true)"
                        pure (B.pack ("(" ++ concat ["(" ++ T.unpack name ++ " " ++ value name ++ ")" | name <- names] ++ ")"))
                    | otherwise = atomicModifyIORef' checks $ \remaining -> case remaining of
                        response : rest -> (rest, response)
                        [] -> error "unexpected check-sat in opaque local witness test"
            solver <- fakeSolver send
            (accepted, counters) <- runFilter context{SMT.ctxSolver = solver} environment $ do
                result <- SM.filterValid F.dummySpan [] F.PTrue [(F.PFalse, 0 :: Int), (F.PTrue, 1), (F.PFalse, 2)]
                (,) result <$> SM.stats
            accepted @?= [1]
            Stats.numChck counters @?= 3
            readIORef checks >>= (@?= [])
        , testCase "a proved first member survives later countermodels and duplicate payloads" $ withContext $ \context -> do
            checks <- newIORef (["unsat", "sat", "unsat"] :: [B.ByteString])
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = do
                        let names = drop 1 (T.words (T.map (\c -> if c == '(' || c == ')' then ' ' else c) (render bytes)))
                            value name = if name `elem` map (F.symbolSmtText . candidateName) [3] then "true" else "false"
                        names @?= map (F.symbolSmtText . candidateName) [1, 2, 3]
                        pure (B.pack ("(" ++ concat ["(" ++ T.unpack name ++ " " ++ value name ++ ")" | name <- names] ++ ")"))
                    | otherwise = atomicModifyIORef' checks $ \remaining -> case remaining of
                        response : rest -> (rest, response)
                        [] -> error "unexpected check-sat after an accepted prefix"
            solver <- fakeSolver send
            (accepted, counters) <- runFilter context{SMT.ctxSolver = solver} environment $ do
                result <- SM.filterValid F.dummySpan [] F.PTrue [(F.PTrue, 4 :: Int), (F.PFalse, 7), (F.PFalse, 7), (F.PTrue, 4)]
                (,) result <$> SM.stats
            accepted @?= [4, 4]
            Stats.numChck counters @?= 3
            readIORef checks >>= (@?= [])
        , testCase "an independently accepted prefix survives later incomplete observations and countermodels" $ withContext $ \context -> do
            checks <- newIORef (["unsat", "unknown", "sat", "unsat"] :: [B.ByteString])
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = do
                        let names = drop 1 (T.words (T.map (\c -> if c == '(' || c == ')' then ' ' else c) (render bytes)))
                            value name = if name == F.symbolSmtText (candidateName 3) then "true" else "false"
                        names @?= map (F.symbolSmtText . candidateName) [2, 3]
                        pure (B.pack ("(" ++ concat ["(" ++ T.unpack name ++ " " ++ value name ++ ")" | name <- names] ++ ")"))
                    | otherwise = atomicModifyIORef' checks $ \responses -> case responses of
                        response : rest -> (rest, response)
                        [] -> error "unexpected check-sat after independently accepting a prefix"
            solver <- fakeSolver send
            (accepted, counters) <- runFilter context{SMT.ctxSolver = solver} environment $ do
                result <- SM.filterValid F.dummySpan [] F.PTrue [(F.PTrue, 4 :: Int), (F.PFalse, 7), (F.PFalse, 7), (F.PTrue, 4)]
                (,) result <$> SM.stats
            accepted @?= [4, 4]
            Stats.numChck counters @?= 4
            readIORef checks >>= (@?= [])
        , testCase "unsupported later models do not discard a proved first member" $ withContext $ \context -> do
            checks <- newIORef (["unsat", "sat"] :: [B.ByteString])
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = pure "unsupported"
                    | otherwise = atomicModifyIORef' checks $ \remaining -> case remaining of
                        response : rest -> (rest, response)
                        [] -> error "unexpected check-sat while preserving a valid first member"
            solver <- fakeSolver send
            (accepted, counters) <- runFilter context{SMT.ctxSolver = solver} environment $ do
                result <- SM.filterValid F.dummySpan [] F.PTrue [(F.PTrue, 4 :: Int), (F.PFalse, 7)]
                (,) result <$> SM.stats
            accepted @?= [4]
            Stats.numChck counters @?= 2
            readIORef checks >>= (@?= [])
        , testGroup
            "SAT witness does not suppress invalid model replies"
            [ testCase label $ withContext $ \context -> do
                checks <- newIORef (0 :: Int)
                let send bytes
                        | "(get-value" `T.isInfixOf` render bytes = pure model
                        | otherwise = do
                            atomicModifyIORef' checks (\count -> (count + 1, ()))
                            pure "sat"
                solver <- fakeSolver send
                outcome <- try (runFilter context{SMT.ctxSolver = solver} environment (SM.filterValid F.dummySpan [] F.PTrue [(F.PFalse, 0 :: Int), (F.PTrue, 1)]) >>= evaluate . length) :: IO (Either SomeException Int)
                case outcome of
                    Left failure -> assertBool "model failure was replaced by a different error" (diagnostic `isInfixOf` show failure)
                    Right _ -> assertFailure "SAT witness suppressed an invalid model reply"
                readIORef checks >>= (@?= 1)
            | (label, model, diagnostic) <-
                [ ("omitted requested identifier", B.pack ("((" ++ T.unpack (F.symbolSmtText (candidateName 0)) ++ " false))"), "omitted requested identifiers")
                , ("malformed model syntax", "((", "SMTREAD:")
                ]
            ]
        ]

incompleteTests :: TestTree
incompleteTests =
    testGroup
        "incomplete observations preserve later independent proofs"
        [ testCase label $ withContext $ \context -> do
            checks <- newIORef replies
            requested <- newIORef False
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = do
                        atomicModifyIORef' requested (const (True, ()))
                        pure model
                    | otherwise = atomicModifyIORef' checks $ \remaining -> case remaining of
                        response : rest -> (rest, response)
                        [] -> error "unexpected check-sat in incomplete observation test"
            solver <- fakeSolver send
            (accepted, counters) <- runFilter context{SMT.ctxSolver = solver} environment $ do
                result <- SM.filterValid F.dummySpan [] F.PTrue [(F.PFalse, 1 :: Int), (F.PTrue, 0)]
                (,) result <$> SM.stats
            accepted @?= [0]
            Stats.numChck counters @?= 2
            readIORef requested >>= (@?= hasModel)
            readIORef checks >>= (@?= [])
        | (label, replies, model, hasModel) <-
            [ ("UNKNOWN omits only the first member", ["unknown", "unsat"], "", False)
            , ("unsupported models retain the actual individual SAT witness", ["sat", "unsat"], "(error \"models unsupported\")", True)
            , ("bare unsupported models retain the actual individual SAT witness", ["sat", "unsat"], "unsupported", True)
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
                Right _ -> assertFailure "check-sat error was treated as an incomplete model observation"
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
        , testCase "literal-free SAT observations do not interpret opaque false text" $ withContext $ \context -> do
            checks <- newIORef (["sat", "unsat"] :: [B.ByteString])
            let send bytes
                    | "(get-value" `T.isInfixOf` render bytes = do
                        let names = drop 1 (T.words (T.map (\c -> if c == '(' || c == ')' then ' ' else c) (render bytes)))
                            value name = if name == F.symbolSmtText (candidateName 0) then "(ite true false |false|)" else "(ite true true |false|)"
                        pure (B.pack ("(" ++ concat ["(" ++ T.unpack name ++ " " ++ value name ++ ")" | name <- names] ++ ")"))
                    | otherwise = atomicModifyIORef' checks $ \remaining -> case remaining of
                        response : rest -> (rest, response)
                        [] -> error "unexpected check-sat in opaque observation test"
            solver <- fakeSolver send
            result <- runFilter context{SMT.ctxSolver = solver} environment (SM.filterValid F.dummySpan [] F.PTrue [(F.PFalse, 1 :: Int), (F.PTrue, 0)])
            result @?= [0]
            readIORef checks >>= (@?= [])
        ]

withSolver :: Config.SMTSolver -> F.SymEnv -> SM.SolveM () a -> IO a
withSolver solver env action = bracket (SMT.makeContextNoLog cfg) SMT.cleanupContext $ \context ->
    runFilter context env (SM.liftSMT (SMT.smtDecls [("x", F.intSort)]) >> action)
  where
    cfg = Config.defConfig{Config.solver = solver}

-- Independent implication proofs: no observers or model-guided filtering.
pointwise :: [F.Equation] -> F.Expr -> [(F.Expr, a)] -> SM.SolveM ann [a]
pointwise definitions left candidates = SM.liftSMT $ SMT.smtBracket "pointwiseLHS" $ do
    forM_ definitions $ \equation -> SMT.smtDefineFunc (F.eqName equation) (F.eqArgs equation) (F.eqSort equation) (F.eqBody equation)
    SMT.smtAssert left
    retained <- filterM (\(predicate, _) -> SMT.smtBracket "pointwiseRHS" (SMT.smtAssert (F.PNot predicate) >> SMT.smtCheckUnsat)) candidates
    pure (map snd retained)

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
runFilter context env action = evalStateT action (SM.SS context{SMT.ctxSymEnv = env} mempty (C.ElabParam (Config.solverFlags (SMT.config context)) "model filtering" env))

environment :: F.SymEnv
environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("x", F.intSort)]}

candidateName :: Int -> F.Symbol
candidateName = F.intSymbol "lq_candidate_value"

x, nonnegative :: F.Expr
x = F.EVar "x"
nonnegative = F.PAtom F.Ge x (integer 0)

integer :: Int -> F.Expr
integer = F.ECon . F.I . fromIntegral

render :: Builder -> T.Text
render = T.pack . B.unpack . toLazyByteString
