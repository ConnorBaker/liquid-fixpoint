{-# LANGUAGE OverloadedStrings #-}

module NestedKVarActualTests (tests) where

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (sort)
import qualified Language.Fixpoint.Graph as G
import qualified Language.Fixpoint.Horn.Info as Horn
import qualified Language.Fixpoint.Solver as Solver
import Language.Fixpoint.Solver.Eliminate (solverInfo)
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types.Solutions as Sol
import qualified Language.Fixpoint.Types.Visitor as V
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "nested Boolean KVar actuals"
        [ testGroup "dependency ownership" graphTests
        , testGroup "native composition" nativeTests
        , testGroup "repeated RHS occurrences" repeatedRhsTests
        , interpretationTests
        , testGroup
            "scraping preserves nested source obligations"
            [ testCase (show valid) $ do
                let original = negativeActual valid
                    candidates = Horn.scrapeFInfo C.defConfig C.Both original
                    scraped = original{F.quals = F.quals original ++ candidates}
                assertBool "scraping introduced recursive candidates" (all (V.isConc . F.qBody) candidates)
                F.cm scraped @?= F.cm original
                F.bs scraped @?= F.bs original
                F.ws scraped @?= F.ws original
                native C.Z3 C.None False valid scraped
            | valid <- [False, True]
            ]
        ]

-- The programmatic constructor admits multiple RHS applications. They are
-- conjunctive obligations, even when they have the same predicate owner.
-- k(1) && k(0), followed by k(1) => False, has no predicate solution;
-- retaining only the final application would incorrectly infer k(v) = v == 0.
repeatedRhsTests :: [TestTree]
repeatedRhsTests =
    [ testCase label $ do
        let config = C.defConfig{C.solver = C.Z3, C.eliminate = C.None, C.cores = Just 1, C.save = False}
        result <- timeout (20 * 1000000) (Solver.solve config fixture)
        case fmap F.resStatus result of
            Just (F.Safe _) -> assertBool "inconsistent repeated occurrences became Safe" valid
            Just (F.Unsafe _ failures) -> do
                assertBool "lawful repeated occurrences were rejected" (not valid)
                sort (map fst failures) @?= [target]
            other -> assertFailure ("expected a checked repeated-RHS verdict, got " ++ show other)
    | (label, fixture, valid, target) <-
        [ (label, repeatedRhsQuery split actuals, valid, if split then 3 else 2)
        | (label, split, actuals, valid) <-
            [ ("combined 1 then 0 is inconsistent", False, [1, 0], False)
            , ("combined 0 then 1 is inconsistent", False, [0, 1], False)
            , ("the middle of three occurrences is required", False, [0, 1, 0], False)
            , ("separate rows preserve the same obligations", True, [1, 0], False)
            , ("the zero-only obligation has a model", False, [0], True)
            ]
        ]
            ++ [ ("independent qualifier survives all occurrences", retainedRhsQuery True, True, 2)
               , ("failing qualifier is removed independently", retainedRhsQuery False, False, 2)
               , ("earlier repeated actual observes nested weakening", repeatedNestedQuery, False, 3)
               ]
    ]

repeatedRhsQuery :: Bool -> [Integer] -> F.FInfo ()
repeatedRhsQuery split actuals = F.fi constraints declarations mempty mempty mempty mempty [qualifier] mempty True False [] mempty []
  where
    k = F.KV "repeated"
    occurrence actual = F.PKVar k mempty (F.mkKVarSubst [("formal", F.ECon (F.I actual))])
    reft predicate = F.RR F.FInt (F.Reft ("value", predicate))
    writers = if split then map occurrence actuals else [F.PAnd (map occurrence actuals)]
    rows = [(F.PTrue, predicate) | predicate <- writers] ++ [(occurrence 1, F.PFalse)]
    constraints = [F.mkSubC mempty (reft lhs) (reft rhs) (Just identifier) [0] () | (identifier, (lhs, rhs)) <- zip [1 ..] rows]
    declarations = F.wfC mempty (F.RR F.FInt (F.Reft ("formal", F.PKVar k mempty mempty))) ()
    qualifier = F.Q "Zero" [F.QP "v" F.PatNone F.FInt] (F.EEq (F.EVar "v") (F.ECon (F.I 0))) (F.dummyPos "repeated-rhs")

-- The same original qualifier payload must be tested at all three actuals:
-- Nonnegative survives, whereas Zero fails only at the middle occurrence.
retainedRhsQuery :: Bool -> F.FInfo ()
retainedRhsQuery valid =
    original
        { F.quals = F.quals original ++ [nonnegative]
        , F.cm = M.adjust (\c -> c{F.slhs = reft observed, F.srhs = reft goal}) 2 (F.cm original)
        }
  where
    original = repeatedRhsQuery False [0, 1, 0]
    reft predicate = F.RR F.FInt (F.Reft ("value", predicate))
    observed = F.PKVar (F.KV "repeated") mempty (F.mkKVarSubst [("formal", value)])
    goal = F.PAtom (if valid then F.Ge else F.Eq) value (F.ECon (F.I 0))
    nonnegative = F.Q "Nonnegative" [F.QP "v" F.PatNone F.FInt] (F.PAtom F.Ge (F.EVar "v") (F.ECon (F.I 0))) (F.dummyPos "repeated-rhs")

-- The last actual always satisfies H(p) = not p. The earlier actual ceases
-- to satisfy it when R weakens, so dropping only by the last actual is unsound.
repeatedNestedQuery :: F.FInfo ()
repeatedNestedQuery =
    query
        [ (1, F.PTrue, F.PAnd [at h (at r F.PTrue), at h F.PFalse])
        , (2, F.PTrue, at r F.PTrue)
        , (3, at h F.PTrue, F.PFalse)
        ]
        (F.PNot $ F.EVar "v")

interpretationTests :: TestTree
interpretationTests =
    testGroup
        "fixed-solution interpretation"
        [ testCase "nested source predicates produce a concrete result" $
            interpret (F.PNot (at h (at r value))) @?= F.PNot value
        , testCase "quantifiers retain their lexical actuals" $
            case interpret (F.PAll [("value", F.boolSort)] (at h (at r value))) of
                F.PAll [(bound, sort)] body -> do
                    sort @?= F.boolSort
                    body @?= F.EVar bound
                result -> assertFailure ("unexpected quantified predicate: " ++ show result)
        , testCase "let substitution does not capture its normalized actual" $ do
            let input = F.ELet "local" (at r (F.EVar "free")) (F.PAll [("free", F.boolSort)] (F.PIff (at h (F.EVar "local")) (F.EVar "free")))
                output = interpret input
            assertBool "solution left a predicate unknown" (V.isConc output)
            F.syms output @?= S.singleton "free"
            case output of
                F.PAll [(bound, _)] (F.PIff (F.EVar free) (F.EVar local)) -> do
                    free @?= "free"
                    local @?= bound
                    assertBool "let actual was captured" (bound /= free)
                _ -> assertFailure ("unexpected scoped predicate: " ++ show output)
        , testCase "qualifier type substitution is applied once" $
            Solution.applyExpr C.defConfig environment typed (F.PKVar h (M.singleton "element" F.boolSort) (F.mkKVarSubst [("formal", value)]))
                @?= F.ECst value F.boolSort
        ]
  where
    environment :: Solution.CombinedEnv ()
    environment = Solution.combinedEnv info (S.fromList ["value", "free", "local"]) mempty F.dummySpan mempty mempty
    info = mempty{F.ws = M.fromList [(k, F.WfC mempty [("formal", F.boolSort)] (k) ()) | k <- [h, r]]}
    qualifier = Sol.trueEqual{Sol.eqPred = F.EVar "formal"}
    solution = Sol.Sol (M.fromList [(h, Sol.QB [qualifier]), (r, Sol.QB [qualifier])]) mempty mempty
    typed = solution{Sol.sMap = M.singleton h (Sol.QB [qualifier{Sol.eqPred = F.ECst (F.EVar "formal") (F.FObj "element")}])}
    interpret = Solution.applyExpr C.defConfig environment solution

h, r :: F.KVar
h = F.KV "outer"
r = F.KV "inner"

at :: F.KVar -> F.Expr -> F.Expr
at unknown argument = F.PKVar unknown mempty (F.mkKVarSubst [("formal", argument)])

value :: F.Expr
value = F.EVar "value"

query :: [(Integer, F.Expr, F.Expr)] -> F.Expr -> F.FInfo ()
query rows candidate = F.fi constraints declarations mempty mempty mempty mempty [qualifier] mempty True False [] mempty []
  where
    reft predicate = F.RR F.boolSort (F.Reft ("value", predicate))
    constraints = [F.mkSubC mempty (reft lhs) (reft rhs) (Just identifier) [0] () | (identifier, lhs, rhs) <- rows]
    declarations = concatMap (\k -> F.wfC mempty (F.RR F.boolSort (F.Reft ("formal", F.PKVar k mempty mempty))) ()) [h, r]
    -- Already-generalized Bool fixture; these tests exercise KVar dependencies.
    qualifier = F.Q "Predicate" [F.QP "v" F.PatNone F.boolSort] candidate (F.dummyPos "nested-kvar-actual")

-- True => H(R(True)); True => R(True); H(True) => False is inconsistent.
-- H(p) = not p initially passes the first row while R(True) is False.
-- Weakening R must revisit that row; checking just the final row is unsound.
-- Its satisfiable dual uses H(False) => False and the candidate H(p) = p.
staleQuery :: Bool -> F.FInfo ()
staleQuery valid =
    query
        [ (1, F.PTrue, at h (at r F.PTrue))
        , (2, F.PTrue, at r F.PTrue)
        , (3, at h (if valid then F.PFalse else F.PTrue), F.PFalse)
        ]
        (if valid then F.EVar "v" else F.PNot $ F.EVar "v")

-- Negation in a nested actual must also observe the current solution.
-- These acyclic controls do not assert completeness for negative cycles:
-- finite qualifier descent need not find every satisfying predicate model.
negativeActual :: Bool -> F.FInfo ()
negativeActual valid =
    ( query
        [ (1, F.PTrue, at h (F.PNot (at r F.PTrue)))
        , (2, F.PTrue, at r F.PTrue)
        , (3, if valid then F.PNot (at h F.PFalse) else at h F.PFalse, F.PFalse)
        ]
        F.PTrue
    )
        { F.quals =
            [ F.Q name [F.QP "v" F.PatNone F.boolSort] predicate (F.dummyPos "negative-kvar-actual")
            | (name, predicate) <- [("Positive", F.EVar "v"), ("Negative", F.PNot (F.EVar "v"))]
            ]
        }

data Nesting = RightActual | LeftActual | SameOwner | Mutual | QuantifiedActual | LetActual deriving (Eq, Show)

nestedQuery :: Nesting -> Bool -> F.FInfo ()
nestedQuery nesting valid = query (definitions ++ [(3, observed, target)]) (F.EVar "v")
  where
    target = if nesting == QuantifiedActual then (if valid then F.PTrue else F.PFalse) else (if valid then value else F.PNot value)
    definitions = case nesting of
        RightActual -> [(1, value, at r value), (2, value, at h (at r value))]
        LeftActual -> [(1, value, at r value), (2, value, at h value)]
        SameOwner -> [(1, value, at h value), (2, value, at h (at h value))]
        Mutual -> [(1, value, at h (at r value)), (2, value, at r (at h value))]
        QuantifiedActual -> [(1, value, at r value), (2, value, at h value)]
        LetActual -> [(1, value, at r value), (2, value, at h value)]
    observed = case nesting of
        LeftActual -> at h (at r value)
        SameOwner -> at h (at h value)
        QuantifiedActual -> F.PAll [("bound", F.boolSort)] (F.PIff (at h (at r (F.EVar "bound"))) (F.EVar "bound"))
        LetActual -> F.ELet "bound" value (at h (at r (F.EVar "bound")))
        _ -> at h value

-- The same dependency can be an ordinary WF parameter, not just the
-- distinguished value parameter. Sanitation must keep scoped compound actuals.
parameterQuery :: Bool -> F.FInfo ()
parameterQuery valid =
    F.fi constraints declarations bindings mempty mempty mempty [qualifier] mempty True False [] mempty []
  where
    (parameterId, bindings) = F.insertBindEnv "parameter" (F.trueSortedReft F.boolSort) () mempty
    scope = F.insertsIBindEnv [parameterId] mempty
    reft predicate = F.RR F.boolSort (F.Reft ("value", predicate))
    application k argument = F.PKVar k mempty (F.mkKVarSubst [("parameter", argument)])
    rows =
        [ (1, F.PTrue, application h (application r F.PTrue))
        , (2, F.PTrue, application r F.PTrue)
        , (3, application h (if valid then F.PFalse else F.PTrue), F.PFalse)
        ]
    constraints = [F.mkSubC scope (reft lhs) (reft rhs) (Just identifier) [0] () | (identifier, lhs, rhs) <- rows]
    declarations = concatMap (\k -> F.wfC scope (F.RR F.boolSort (F.Reft ("formal", F.PKVar k mempty mempty))) ()) [h, r]
    qualifier = F.Q "Parameter" [F.QP "v" F.PatNone F.boolSort, F.QP "p" F.PatNone F.boolSort] (if valid then F.EVar "p" else F.PNot (F.EVar "p")) (F.dummyPos "nested-kvar-parameter")

nativeTests :: [TestTree]
nativeTests =
    [ testCase (name ++ " / " ++ show (solver, elimination, slicing, valid)) (native solver elimination slicing valid original)
    | solver <- [C.Z3, C.Cvc5]
    , elimination <- [C.None, C.Some, C.All]
    , slicing <- [True, False]
    , valid <- [True, False]
    , (name, original) <- [("stale read and satisfiable dual", staleQuery valid), ("ordinary WF parameter", parameterQuery valid), ("negative actual and satisfiable dual", negativeActual valid)] ++ [(show nesting, nestedQuery nesting valid) | nesting <- [RightActual, LeftActual, SameOwner, Mutual, QuantifiedActual, LetActual]]
    ]

native :: C.SMTSolver -> C.Eliminate -> Bool -> Bool -> F.FInfo () -> Assertion
native solver elimination slicing valid original = do
    let cfg = C.defConfig{C.solver = solver, C.eliminate = elimination, C.cores = Just 1, C.srcFile = "nested-kvar-actual", C.noslice = not slicing}
    result <- timeout (20 * 1000000) (Solver.solve cfg original)
    case fmap F.resStatus result of
        Just (F.Safe _) -> assertBool "false result became Safe" valid
        Just (F.Unsafe _ failures) -> do
            assertBool ("lawful nested composition was rejected: " ++ show result) (not valid)
            sort (map fst failures) @?= [3]
        other -> assertFailure ("expected a checked verdict, got " ++ show other)

graphTests :: [TestTree]
graphTests =
    [ testCase "occurrence collection retains distinct applications of the same predicate" $
        fmap length (M.lookup r (F.exprKVars (F.PAnd [at r F.PTrue, at r F.PFalse]))) @?= Just 2
    , testCase "RHS actual is a read, never a write of its surrounding row" $ do
        let edges = G.kvEdges (staleQuery False)
        assertBool "missing nested read" ((G.KVar r, G.Cstr 1) `elem` edges)
        assertBool "missing outer write" ((G.Cstr 1, G.KVar h) `elem` edges)
        assertBool "nested read misclassified as write" ((G.Cstr 1, G.KVar r) `notElem` edges)
    , testCase "LHS observes both the outer predicate and its actual" $ do
        let edges = G.kvEdges (nestedQuery LeftActual True)
        assertBool "missing outer LHS read" ((G.KVar h, G.Cstr 3) `elem` edges)
        assertBool "missing nested LHS read" ((G.KVar r, G.Cstr 3) `elem` edges)
    , testCase "slicing preserves nested definitions, declarations, and actuals" $ do
        let original = staleQuery False
            sliced = G.slice C.defConfig original
        sort (M.keys $ F.cm sliced) @?= [1, 2, 3]
        M.keysSet (F.ws sliced) @?= S.fromList [h, r]
        F.crhs (F.cm sliced M.! 1) @?= F.crhs (F.cm original M.! 1)
    , testCase "partition preserves the nested writer and both declarations" $ do
        let original = staleQuery False
        case G.partition' Nothing original of
            [part] -> do
                sort (M.keys $ F.cm part) @?= [1, 2, 3]
                M.keysSet (F.ws part) @?= S.fromList [h, r]
                F.crhs (F.cm part M.! 1) @?= F.crhs (F.cm original M.! 1)
            parts -> assertFailure ("expected one jointly owned partition, got " ++ show (length parts))
    , testCase "Cube exclusion is local to the unsupported actual owner" $ do
        (_, _, canonical, _) <- Solver.simplifyFInfo C.defConfig (staleQuery False)
        let result = solverInfo C.defConfig{C.eliminate = C.All, C.autoKuts = True} canonical
        G.siVars result @?= S.singleton h
        M.keysSet (Sol.sHyp $ G.siSol result) @?= S.singleton r
        assertBool "outer defining row disappeared" (M.member 1 $ F.cm $ G.siQuery result)
    , testCase "nested use actuals still permit ordinary definition elimination" $ do
        (_, _, canonical, _) <- Solver.simplifyFInfo C.defConfig (nestedQuery LeftActual True)
        let result = solverInfo C.defConfig{C.eliminate = C.All, C.autoKuts = True} canonical
        G.siVars result @?= mempty
        M.keysSet (Sol.sHyp $ G.siSol result) @?= S.fromList [h, r]
    , testCase "an inferred sink remains in elimination and worklist domains" $ do
        let original =
                (query [(1, F.PTrue, at r F.PFalse), (2, at r value, at h value)] (F.EVar "v"))
                    { F.kuts = F.KS (S.singleton r)
                    }
            config = C.defConfig{C.eliminate = C.Some, C.noslice = True}
        (_, _, canonical, _) <- Solver.simplifyFInfo config original
        let result = solverInfo config canonical
            constraints = M.keysSet (F.cm $ G.siQuery result)
            successors = G.cSucc (G.siDeps result)
        G.siVars result @?= S.singleton r
        M.keysSet (Sol.sHyp $ G.siSol result) @?= S.singleton h
        assertBool
            "a dependency schedules an eliminated defining constraint"
            (S.fromList (concat $ M.elems successors) `S.isSubsetOf` constraints)
    ]
