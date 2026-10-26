{-# LANGUAGE OverloadedStrings #-}

module SolutionPresentationTests (tests) where

import Control.Exception (SomeException, evaluate, try)
import qualified Data.ByteString.Char8 as Bytes
import Data.Char (isSpace)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Language.Fixpoint.Parse (rr')
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types.Visitor as V
import qualified Language.Fixpoint.Utils.Files as Files
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import qualified Text.PrettyPrint.HughesPJ as PJ

tests :: TestTree
tests =
    testGroup
        "solution presentation"
        [ testCase "saved cuts and delayed closures retain every scoped token" $ do
            let variable = F.KV "presentation"
                body = closure 4
                formals = [F.Formal "source" "canonical" F.FInt]
                result = F.Result (F.Safe mempty) (M.singleton variable body) (M.singleton variable (F.Delayed body)) (M.singleton variable formals) :: F.Result ()
                entry = PJ.render (PJ.hsep [F.pprint variable PJ.<> F.pprint [("canonical" :: F.Symbol, F.FInt)], PJ.text ":=", F.pprint body])
                expected = "Solution:" ++ entry ++ "Non-cut kvars:" ++ entry
            save result $ \output ->
                filter (not . isSpace) (Bytes.unpack output) @?= filter (not . isSpace) expected
        , testCase "saved lexical sharing has a linear wire bound" $ do
            let saved depth = F.Result (F.Safe mempty) mempty (M.singleton (F.KV "presentation") (F.Delayed (closure depth))) mempty :: F.Result ()
            save (saved 64) $ \small ->
                save (saved 256) $ \large -> do
                    assertBool "padding must not dominate lexical definitions" (Bytes.length large < 256 * 300)
                    assertBool "four times the definitions must not square the wire size" (Bytes.length large < 5 * Bytes.length small)
        , -- LiquidHaskell prints solutions in its error contexts with pprint,
          -- in page mode, not with the saved file's LeftMode.
          -- The layout may change only whitespace: the tokens must be the ones
          -- the horizontal printer printed, captured from it (65fd562c), not
          -- the current Doc rendered another way.
          testCase "printed lexical sharing has a linear page-mode size" $ do
            let printed depth = F.showpp (closure depth)
            words (printed 2) @?= horizontalTokens
            assertBool "four times the definitions must not square the printed size" (length (printed 256) < 5 * length (printed 64))
        , -- closure's lambdas bind one formal each; an exported summary's bind
          -- one per formal, so their order is part of the printed tokens.
          testCase "printed lambda chains keep their binders' order" $
            words (F.showpp binderChain) @?= horizontalBinderTokens
        , testGroup "ordered comparisons of a non-numeric carrier" $
            [ testCase ("presented " ++ label ++ " solution has its source operands") $ do
                (solution, formals) <- solved sorted
                assertBool ("elaboration cast leaked: " ++ F.showpp solution) (not (S.member F.toIntName (F.syms solution)))
                V.stripCasts solution @?= F.PAtom F.Ge (F.EVar (canonical "v" formals)) (F.EVar (canonical "x" formals))
            | (label, sorted) <- [("sorted", True), ("unsorted", False)]
            ]
                ++ [ testCase "a sorted solution is a premise of a later query" $
                        reused True >>= (@?= Right True)
                   , testCase "a reused premise does not prove the converse comparison" $
                        reused False >>= (@?= Right False)
                   ]
        ]

-- The query infers $k0 := v >= x over Bool. Ordering a non-numeric carrier
-- elaborates each operand through the solver's integer cast.
orderedQuery :: F.FInfo ()
orderedQuery =
    rr' "ordered-bool" $
        unlines
            [ "qualif AtLeast(v:bool, x:bool) { v >= x }"
            , "bind 0 x : {v : bool | true}"
            , "constraint: env [0] lhs {v : bool | v >= x} rhs {v : bool | $k0} id 1 tag []"
            , "constraint: env [0] lhs {v : bool | $k0} rhs {v : bool | v >= x} id 2 tag []"
            , "wf: env [0] reft {v : bool | $k0}"
            ]

solved :: Bool -> IO (F.Expr, [F.Formal])
solved sorted = do
    result <- Solver.solve C.defConfig{C.save = False, C.sortedSolution = sorted} orderedQuery
    assertBool "the ordered query must be safe" (F.isSafe result)
    case M.toList (F.resSolution result) of
        [(k, solution)] -> pure (solution, M.lookupDefault [] k (F.resScopes result))
        other -> assertFailure ("expected one solved KVar, got " ++ show (length other)) >> fail "solution"

canonical :: F.Symbol -> [F.Formal] -> F.Symbol
canonical source formals = case [F.formalCanonical f | f <- formals, F.formalSource f == source] of
    [name] -> name
    _ -> error ("no formal for " ++ show source)

-- A later query assumes the sorted solution for y, as a client re-feeding an
-- inferred type does, and checks y >= x (implied) or x >= y (not implied).
-- Right reports the verdict; Left is a crash.
reused :: Bool -> IO (Either String Bool)
reused implied = do
    (solution, formals) <- solved True
    let premise = F.subst (F.mkSubst [(F.formalCanonical f, F.EVar (F.formalSource f)) | f <- formals]) solution
        goal = if implied then "v >= x" else "x >= v"
        base =
            rr' "reused-solution" $
                unlines
                    [ "bind 0 x : {v : bool | true}"
                    , "bind 1 y : {v : bool | true}"
                    , "constraint: env [0; 1] lhs {v : bool | v = y} rhs {v : bool | " ++ goal ++ "} id 1 tag []"
                    ] :: F.FInfo ()
        query = base{F.bs = F.bindEnvFromList [(0, ("x", F.trueSortedReft F.boolSort, ())), (1, ("y", F.RR F.boolSort (F.Reft ("v", premise)), ()))]}
    outcome <- try (Solver.solve C.defConfig{C.save = False} query >>= evaluate) :: IO (Either SomeException (F.Result (Integer, ())))
    pure $ case fmap F.resStatus outcome of
        Left failure -> Left (show failure)
        Right (F.Safe _) -> Right True
        Right (F.Unsafe _ _) -> Right False
        Right status -> Left (take 400 (show (fmap (const ()) status)))

save :: F.Result () -> (Bytes.ByteString -> IO ()) -> IO ()
save result observe = withSystemTempDirectory "solution-presentation" $ \directory -> do
    let source = directory </> "Presentation.hs"
    Solution.saveSolution C.defConfig{C.save = True, C.srcFile = source} "" result
    Bytes.readFile (Files.tempFileName (source ++ ".fqout")) >>= observe

-- @words (F.showpp (closure 2))@ as the printer before the let and lambda
-- layout printed it, each body after its header on one run.
horizontalTokens :: [String]
horizontalTokens =
    [ "(let)", "shared_predicate_0", "=", "lam", "argument_0", ":", "int", ".", "exists", "[witness_0", ":", "int]", "."
    , "witness_0", "==", "argument_0", "&&", "argument_0", "==", "1"
    , "in", "(let)", "shared_predicate_1", "=", "lam", "argument_1", ":", "int", ".", "exists", "[witness_1", ":", "int]", "."
    , "witness_1", "==", "argument_1", "&&", "shared_predicate_0", "argument_1"
    , "in", "shared_predicate_1", "1"
    ]

-- A let-bound chain of three lambdas, the shape an exported summary takes
-- (one lambda per formal), applied to three arguments.
binderChain :: F.Expr
binderChain = F.ELet "f" (foldr lam body [0 .. 2 :: Int]) (foldl F.EApp (F.EVar "f") [F.ECon (F.I n) | n <- [1 .. 3]])
  where
    binder i = F.symbol ("x_" ++ show i)
    lam i = F.ELam (binder i, F.FInt)
    body = F.PAnd [F.PAtom F.Eq (F.EVar (binder 0)) (F.ECon (F.I 1)), F.PAtom F.Gt (F.EVar (binder 2)) (F.ECon (F.I 0))]

-- @words (F.showpp binderChain)@ as the printer before the let and lambda
-- layout printed it.
horizontalBinderTokens :: [String]
horizontalBinderTokens =
    [ "(let)", "f", "=", "lam", "x_0", ":", "int", ".", "lam", "x_1", ":", "int", ".", "lam", "x_2", ":", "int", "."
    , "x_0", "==", "1", "&&", "x_2", ">", "0"
    , "in", "f", "1", "2", "3"
    ]

closure :: Int -> F.Expr
closure depth = foldr define (F.EApp (F.EVar (name (depth - 1))) (F.ECon (F.I 1))) [0 .. depth - 1]
  where
    name index = F.symbol ("shared_predicate_" ++ show index)
    define index continuation =
        let argument = F.symbol ("argument_" ++ show index)
            witness = F.symbol ("witness_" ++ show index)
            previous = if index == 0 then F.PAtom F.Eq (F.EVar argument) (F.ECon (F.I 1)) else F.EApp (F.EVar (name (index - 1))) (F.EVar argument)
            body = F.PExist [(witness, F.FInt)] (F.PAnd [F.PAtom F.Eq (F.EVar witness) (F.EVar argument), previous])
         in F.ELet (name index) (F.ELam (argument, F.FInt) body) continuation
