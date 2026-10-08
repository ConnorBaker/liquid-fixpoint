{-# LANGUAGE OverloadedStrings #-}

module EliminatedSharingTests (tests, diamond, exportedBody) where

import Control.DeepSeq (force)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM_)
import qualified Data.Aeson as Json
import qualified Data.ByteString.Lazy as Bytes
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import EliminatedSharingSupport
import qualified Language.Fixpoint.Graph as Graph
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Eliminate as Eliminate
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.SortCheck as So
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types.Solutions as Sol
import qualified Language.Fixpoint.Types.Visitor as V
import NativeCallableTests (withSMT)
import SortInventoryTests (allocationBytes)
import qualified SummaryScopeTests
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertEqual, assertFailure, testCase, testCaseInfo, (@?=))

tests :: TestTree
tests =
    testGroup
        "eliminated predicate sharing"
        ( [ testCase label (check label expected (depth <= 4) (diamond depth target))
          | depth <- [1, 4, 8, 12]
          , (target, expected) <- [(0, True), (1, False)]
          , let label = "diamond " ++ show depth ++ " target " ++ show target
          ]
            ++ [ testCase label (check label expected True fixture)
               | (label, expected, fixture) <-
                    [ ("existential cannot capture external one", True, capture 1)
                    , ("existential cannot capture external zero", False, capture 0)
                    , ("closed Bool specialization", True, poly F.boolSort False)
                    , ("closed Int specialization", False, poly F.FInt False)
                    , ("nested Bool specialization", True, poly F.boolSort True)
                    , ("nested Int specialization", False, poly F.FInt True)
                    , ("missing global actual stays filtered", True, globalActual False)
                    , ("present global actual stays observed", False, globalActual True)
                    , ("multiple cubes retain filtered actual", True, multiCubeActual False)
                    , ("multiple cubes retain observed actual", False, multiCubeActual True)
                    ]
               ]
            ++ [ testCase label (check label (defined /= actual) True (cubeBinderOwnership defined actual))
               | defined <- [False, True]
               , actual <- [False, True]
               , let label = "cube existential owns shadowed sort " ++ show (defined, actual)
               ]
            ++ [ testCase label (check label expected (depth <= 4) (diamondActual depth target))
               | depth <- [4, 12]
               , (target, expected) <- [(0, True), (1, False)]
               , let label = "Boolean actual diamond " ++ show depth ++ " target " ++ show target
               ]
            ++ [ testCase ("solve " ++ show mode ++ " target " ++ show target) $ do
                    result <- Solver.solve cfg{C.eliminate = mode, C.cores = Just 1} (diamondQuery 8 target)
                    case (target, F.resStatus result) of
                        (0, F.Safe _) -> pure ()
                        (1, F.Unsafe _ _) -> pure ()
                        _ -> fail ("unexpected solve result: " ++ show (F.resStatus result))
               | mode <- [C.Some, C.All]
               , target <- [0, 1]
               ]
            ++ [ testCase ("native function actual " ++ show mode ++ " expected " ++ show value) $ do
                    result <- Solver.solve cfg{C.eliminate = mode, C.cores = Just 1, C.explicitKvars = True} (nativeFunctionQuery value)
                    case (value, F.resStatus result) of
                        (0, F.Safe _) -> pure ()
                        (1, F.Unsafe _ _) -> pure ()
                        _ -> assertFailure ("unexpected native function result: " ++ show (F.resStatus result))
               | mode <- [C.Some, C.All]
               , value <- [0, 1]
               ]
            ++ [ testCase ("numeric alias through elimination " ++ show mode ++ " offset " ++ show value) (numericAliasElimination mode value)
               | mode <- [C.Some, C.All]
               , value <- [0, 1]
               ]
            ++ [ testCase ("native global through elimination " ++ show mode ++ " shape " ++ show shape ++ " relation " ++ show relation) (globalElimination "Method" (nativeGlobalQuery True shape relation) mode relation)
               | mode <- [C.Some, C.All]
               , shape <- [0, 1, 2]
               , relation <- [F.Eq, F.Ne]
               ]
            ++ [ testCase ("ordinary polymorphic global through elimination " ++ show mode ++ " relation " ++ show relation) (globalElimination "empty" (polymorphicGlobalQuery True relation) mode relation)
               | mode <- [C.Some, C.All]
               , relation <- [F.Eq, F.Ne]
               ]
            ++ [ testCase ("cube-bound function " ++ show name ++ " " ++ show mode ++ " value " ++ show value) (cubeLocalFunction name mode value)
               | name <- ["bool_to_int", "cube_function"]
               , mode <- [C.Some, C.All]
               , value <- [0, 1]
               ]
            ++ [ testCase ("native result index " ++ show mode ++ " conclusion " ++ show conclusion) (indexedDefinitionResult mode conclusion)
               | mode <- [C.Some, C.All]
               , conclusion <- [False, True]
               ]
            ++ [ testCase ("defining type substitution cut " ++ show instantiated) (indexedDefinitionCut instantiated)
               | instantiated <- [False, True]
               ]
            ++ [ SummaryScopeTests.tests
               , testCase "exported solution closes common locals, not formals or globals" (forM_ [False, True] exportedSolution)
               , testCase "defining-only ordinary global stays fixed" (globalElimination "empty" (polymorphicGlobalQuery False F.Eq) C.Some F.Eq)
               , testCase "defining-only native constructor stays fixed" (globalElimination "Method" (nativeGlobalQuery False 0 F.Ne) C.Some F.Ne)
               , testCase "consumer binders cannot capture definition names" (forM_ [False, True] declaredGlobalShadow)
               , testCase "solver boundary removes invented global substitutions" normalizedFormals
               , testCase "numeric-first specialization preserves actual admission" (specializedCapabilityAdmission True)
               , testCase "opaque-first specialization preserves actual admission" (specializedCapabilityAdmission False)
               , testCase "solver boundary rejects undeclared concrete globals" $
                    mustThrow $ do
                        (_, _, prepared, _) <- Solver.simplifyFInfo cfg (withUnknownGlobal (diamondQuery 1 0))
                        evaluate (force prepared)
               , testCase "diamond summaries grow linearly" $
                    forM_ [4, 8, 16] $ \depth ->
                        assertEqual "one definition per level" (depth + 1) (summaryCount (diamond depth 0))
               , testCase "Boolean actual summaries grow linearly" $
                    forM_ [4, 8, 16] $ \depth ->
                        assertEqual "one definition per level and outer use" (depth + 2) (summaryCount (diamondActual depth 0))
               , testGroup
                    "exported closures"
                    ( [ testCase ("complete nested witnesses " ++ show (depth, common)) (exportedDiamond depth common)
                      | depth <- [1, 4]
                      , common <- [False, True]
                      ]
                        ++ [testCase "deep Expr, JSON and term transport stay linear" exportedGrowth]
                        ++ [ testCase ("defining Boolean actual " ++ show value) (exportedDefiningActual value)
                           | value <- [0, 1]
                           ]
                        ++ [ testCase ("type transport " ++ show (sort, nested)) (exportedType sort nested)
                           | sort <- [F.boolSort, F.FInt]
                           , nested <- [False, True]
                           ]
                    )
               , testCase "repeated observations share the query inventory" inventoryAllocation
               , testGroup
                    "repeated actuals share their declaration scope"
                    [testCaseInfo ("explicit KVars: " ++ show explicit) (declarationAllocation explicit) | explicit <- [False, True]]
               , testCase "declaration preparation preserves scope extension and duplicate owners" declarationScopes
               , testCase "query inventory does not share predicate definitions" inventorySolutions
               , testCase "forcing Result preserves optional delayed body" $ do
                    _ <- evaluate (force delayedResult)
                    pure ()
               , testCase "forcing Result still observes malformed verdict" $
                    mustThrow (evaluate (force (delayedResult{F.resStatus = error "malformed verdict"} :: F.Result ())))
               , testCase "explicit forceDelayed observes malformed payload" $
                    mustThrow (evaluate (force (F.forceDelayed delayedBody)))
               , testCase "requested JSON observes malformed payload" $
                    mustThrow (evaluate (Bytes.length (Json.encode delayedResult)))
               ]
        )

delayedBody :: F.Delayed F.Expr
delayedBody = F.Delayed (error "malformed optional predicate")

delayedResult :: F.Result ()
delayedResult = F.Result (F.Safe mempty) mempty (M.singleton (kvar 0) delayedBody) mempty

mustThrow :: IO a -> Assertion
mustThrow action = do
    outcome <- try (action >> pure ()) :: IO (Either SomeException ())
    case outcome of
        Left _ -> pure ()
        Right _ -> assertFailure "expected the explicitly demanded malformed value to fail"

summaryCount :: Fixture -> Int
summaryCount (info, solution, constraint) =
    length . fst $ Solution.lhsPredShared cfg initial scope F.emptyIBindEnv info solution constraint
  where
    bindings = F.bs info
    scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList bindings]
    initial = Solution.prepareSummaryState scope info

exportedBody :: Int -> Fixture -> F.Expr
exportedBody index (info, solution, _) =
    F.forceDelayed (Solution.nonCutsResult cfg scope info solution M.! kvar index)
  where
    scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList (F.bs info)]

-- Public solution expressions are transported back into source predicates;
-- observe them through the real source elaborator, not raw SMT lambda syntax.
elaboratedExport :: F.SInfo () -> F.Expr -> F.Expr
elaboratedExport info predicate = So.elaborateExpr (C.solverFlags cfg) environment mempty "exported closure" predicate (Just F.boolSort)
  where
    theory = So.theoryEnv cfg info
    declarations = F.fromListSEnv [(name, F.sr_sort refinement) | (_, (name, refinement, _)) <- F.bindEnvToList (F.bs info)]
    environment = F.symEnv cfg (declarations <> (F.tsSort <$> theory)) theory (F.ddecls info) mempty

exportedDiamond :: Int -> Bool -> Assertion
exportedDiamond depth common = do
    let (info, solution, constraint) = diamond depth 0
        closed = solution{Sol.sScp = if common then M.map (F.unionsIBindEnv . map Sol.cuBinds) (Sol.sHyp solution) else Sol.sScp solution}
        actual = F.subst1 (exportedBody depth (info, closed, constraint)) (sym "v" depth, var "x")
        scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList (F.bs info)]
        -- The reference's empty common scopes expand every defining witness.
        expected = Solution.lhsPred cfg scope mempty info solution constraint
    equivalent <- valid (info, solution, constraint{F._crhs = F.PFalse}) [] (elaboratedExport info (F.PNot (F.PIff actual expected)))
    assertBool "export equals the complete unfolded relation" equivalent
    assertEqual "no defining witness escapes" (S.singleton "x") (F.syms actual)
    assertEqual "one lexical closure per level" (depth + 1) (letCount actual)

exportedGrowth :: Assertion
exportedGrowth = do
    sizes <- mapM measure [16, 32, 64]
    forM_ (zip sizes (drop 1 sizes)) $ \((nodes, bytes), (nodes', bytes')) -> do
        assertBool "Expr doubling remains linear" (nodes' < 3 * nodes)
        assertBool "JSON doubling remains linear" (bytes' < 3 * bytes)
  where
    measure depth = do
        let body = exportedBody depth (diamond depth 0)
            transported = F.subst1 body (sym "v" depth, var "actual")
            scopes = M.singleton (kvar depth) [F.Formal "source" (sym "v" depth) F.FInt]
            result = F.Result (F.Safe mempty) mempty (M.singleton (kvar depth) (F.Delayed body)) scopes :: F.Result ()
        nodes <- evaluate (V.size body)
        bytes <- evaluate (Bytes.length (Json.encode result))
        assertEqual "all definitions remain shared" (depth + 1) (letCount body)
        assertEqual "term transport preserves graph size" nodes (V.size transported)
        assertEqual "term transport has exact free support" (S.singleton "actual") (F.syms transported)
        pure (nodes, bytes)

exportedType :: F.Sort -> Bool -> Assertion
exportedType sort nested = do
    let fixture@(info, solution, constraint) = poly sort nested
        body = exportedBody (if nested then 1 else 0) fixture
        typed = V.applyCoSub (M.singleton "element" sort) body
    assertEqual "type transport preserves lexical definitions" (letCount body) (letCount typed)
    assertEqual "type transport preserves graph size" (V.size body) (V.size typed)
    valid (info, solution, constraint) [] (elaboratedExport info typed) >>= (@?= (sort == F.boolSort))

letCount :: F.Expr -> Int
letCount = count
  where
    count (F.ELet _ _ body) = 1 + count body
    count _ = 0

exportedDefiningActual :: Integer -> Assertion
exportedDefiningActual value = do
    let depth = 4
        (base, original, constraint) = diamond depth 0
        key = kvar (depth + 1)
        unknown = F.PKVar (kvar depth) mempty (F.mkKVarSubst [(sym "v" depth, int value)])
        info = base{F.bs = F.bindEnvFromList (binding 300 "flag" F.boolSort F.PTrue : F.bindEnvToList (F.bs base)), F.ws = M.insert key (F.WfC mempty [("flag", F.boolSort)] key ()) (F.ws base)}
        cube = Sol.Cube mempty (F.mkSubst [("flag", unknown)]) 300 []
        solution = original{Sol.sHyp = M.insert key [cube] (Sol.sHyp original), Sol.sScp = M.insert key mempty (Sol.sScp original)}
        body = exportedBody (depth + 1) (info, solution, constraint)
        expected = F.EEq (var "flag") (if value == 0 then F.PTrue else F.PFalse)
        collision = F.tempSymbol "eliminated_summary" (0 :: Integer)
        transported = F.subst1 body ("flag", var collision)
    V.kvarsExpr body @?= []
    F.syms body @?= S.singleton "flag"
    F.syms transported @?= S.singleton collision
    letCount body @?= depth + 2
    equivalent <- valid (info, solution, constraint{F._crhs = F.PFalse}) [] (elaboratedExport info (F.PNot (F.PIff body expected)))
    assertBool "defining actual is interpreted before its equality" equivalent

inventoryAllocation :: Assertion
inventoryAllocation = do
    let (originalInfo, solution, constraint) = diamond 0 0
        original = F.bs originalInfo
        scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList original]
        distractors = [binding (1000 + index) (sym "unused" index) F.FInt (F.EEq (var (sym "unused" index)) (int 0)) | index <- [1 .. 4096]]
        bindings = F.bindEnvFromList (F.bindEnvToList original ++ distractors)
        info = originalInfo{F.bs = bindings}
        config = cfg{C.explicitKvars = True}
        initial = Solution.prepareSummaryState scope info
        observe = Solution.lhsPredShared config initial scope mempty info solution
        constraints = [constraint{F._cid = Just index} | index <- [1 .. 64]]
        results = map observe constraints
    _ <- evaluate (force (bindings, solution, scope, constraints))
    bytes <- allocationBytes results
    let reference = Solution.lhsPredShared config (Solution.prepareSummaryState scope originalInfo) scope mempty originalInfo solution constraint
    mapM_ (@?= reference) results
    assertBool ("repeated whole-query inventory allocation: " ++ show bytes) (bytes < 64 * 1024 * 1024)

declarationAllocation :: Bool -> IO String
declarationAllocation explicit = do
    narrowFirst <- observe 256 2
    narrowMany <- observe 256 32
    wideFirst <- observe 4096 2
    wideMany <- observe 4096 32
    let message = "declaration widths/occurrences allocated " ++ show (narrowFirst, narrowMany, wideFirst, wideMany)
    assertBool
        message
        (wideMany <= 4 * wideFirst + 4 * narrowMany + 2 * 1024 * 1024)
    pure message
  where
    observe width count = do
        let actuals = [F.PAtom F.Ge (var "x") (int index) | index <- [1 .. count]]
            occurrences = [F.PKVar (kvar 0) mempty (F.mkKVarSubst [("formal", actual)]) | actual <- actuals]
            unused = [binding (1000 + index) (sym "unused" index) F.FInt F.PTrue | index <- [1 .. width]]
            bindings = F.bindEnvFromList (unused ++ [binding 0 "formal" F.boolSort F.PTrue, binding 1 "witness" F.boolSort (var "witness"), binding 2 "x" F.FInt F.PTrue, binding 3 "target" F.boolSort (F.PAnd occurrences)])
            info = mempty{F.bs = bindings, F.ws = M.singleton (kvar 0) (F.WfC mempty [("formal", F.boolSort)] (kvar 0) ())}
            cube = Sol.Cube (F.fromListIBindEnv [1]) (F.mkSubst [("formal", var "witness")]) 0 []
            solution :: Sol.Solution
            solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) mempty)
            constraint = F.SimpC (F.fromListIBindEnv (2 : 3 : map fst unused)) (F.PAnd actuals) (Just 99) 3 [] ()
            scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList bindings]
            initial = Solution.prepareSummaryState scope info
            result = Solution.lhsPredShared cfg{C.explicitKvars = explicit} initial scope mempty info solution constraint
        _ <- evaluate (force (bindings, solution, constraint, scope, actuals))
        bytes <- allocationBytes result
        case result of
            ([definition], predicate) ->
                F.pAnd [predicate] @?= F.pAnd [F.EApp (var (F.eqName definition)) actual | actual <- actuals]
            _ -> assertFailure "repeated actuals did not share one definition"
        pure bytes

declarationScopes :: Assertion
declarationScopes =
    forM_ cases $ \(label, caller, defining, actual) -> do
        let bindings =
                F.bindEnvFromList
                    [ binding 0 "alpha" F.FNum F.PTrue
                    , binding 1 "x" F.FInt F.PTrue
                    , binding 2 "x" F.boolSort F.PTrue
                    , binding 3 "formal" F.boolSort F.PTrue
                    , binding 4 "target" F.boolSort (F.PKVar (kvar 0) mempty mempty)
                    , binding 5 "alpha" F.FFrac F.PTrue
                    ]
            cube = Sol.Cube (F.fromListIBindEnv defining) (F.mkSubst [("formal", actual)]) 0 []
            info = mempty{F.bs = bindings, F.ws = M.singleton (kvar 0) (F.WfC mempty [("formal", F.boolSort)] (kvar 0) ())}
            solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) mempty)
            constraint = F.SimpC (F.fromListIBindEnv (4 : caller)) F.PTrue (Just 99) 4 [] ()
            scope = S.fromList ["alpha", "x", "formal", "target"]
            declarations = F.sr_sort <$> F.fromListSEnv (F.envCs bindings (F.unionIBindEnv (F.senv constraint) (Sol.cuBinds cube)))
            locals = F.sr_sort <$> F.fromListSEnv (F.envCs bindings (Sol.cuBinds cube))
            expected = either (const False) (== F.boolSort) (So.sortExprE Nothing F.dummySpan declarations locals actual)
            initial = Solution.prepareSummaryState scope info
            (definitions, predicate) = Solution.lhsPredShared cfg initial scope mempty info solution constraint
            define equation = F.ELet (F.eqName equation) (foldr F.ELam (F.eqBody equation) (F.eqArgs equation))
            expanded = Solution.lhsPred cfg scope mempty info solution constraint
        forM_ [expanded, foldr define predicate definitions] $ \body ->
            assertEqual label expected (S.member "formal" (F.syms body))
  where
    cases =
        [ ("new numeric declaration is visible", [], [0], F.EEq (F.ECst (int 0) (F.FObj "alpha")) (int 0))
        , ("new numeric declaration does not admit Bool", [], [0], F.EEq (F.ECst F.PTrue (F.FObj "alpha")) F.PTrue)
        ]
            ++ [ ("duplicate declaration " ++ show sort, [1, 2], [], F.EEq (F.ECst (var "x") sort) value)
               | (sort, value) <- [(F.FInt, int 0), (F.boolSort, F.PTrue)]
               ]
            ++ [ ("split numeric declaration " ++ show caller, caller, defining, F.EEq (F.EBin F.Mod (F.ECst (int 0) (F.FObj "alpha")) (int 1)) (int 0))
               | (caller, defining) <- [([0], [5]), ([5], [0])]
               ]

inventorySolutions :: Assertion
inventorySolutions = do
    let (originalInfo, solution, constraint) = diamond 0 0
        original = F.bs originalInfo
        bindings = F.adjustBindEnv (const ("y0", F.RR F.FInt (F.Reft ("y0", F.PKVar (kvar 1) mempty mempty)))) 1 original
        info = originalInfo{F.bs = bindings, F.ws = M.insert (kvar 1) (F.WfC mempty [("y0", F.FInt)] (kvar 1) ()) (F.ws originalInfo)}
        qualifier = Sol.trueEqual{Sol.eqPred = F.EEq (var "y0") (int 0)}
        before = solution{Sol.sMap = M.singleton (kvar 1) (Sol.QB [qualifier])}
        (_, after) = Sol.update before [(kvar 1, Sol.QB [])]
        scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList bindings]
        initial = Solution.prepareSummaryState scope info
    forM_ [(before, True), (after, False), (before, True)] $ \(current, expected) -> do
        let fixture = (info, current, constraint)
            (definitions, predicate) = Solution.lhsPredShared cfg initial scope mempty info current constraint
        assertBool "the observation requires a local definition" (not (null definitions))
        valid fixture definitions predicate >>= (@?= expected)
        valid fixture [] (Solution.lhsPred cfg scope mempty info current constraint) >>= (@?= expected)

diamond :: Int -> Integer -> Fixture
diamond depth target = (info, solution, constraint)
  where
    info = mempty{F.bs = bindings, F.ws = M.fromList [(kvar index, F.WfC mempty [(sym "v" index, F.FInt)] (kvar index) ()) | index <- [0 .. depth]]}
    base = [binding 1 "y0" F.FInt (F.EEq (var "y0") (int 0))]
    step index =
        [ binding (2 * index) (sym "y" index) F.FInt (use (index - 1) (sym "y" index))
        , binding
            (2 * index + 1)
            (sym "z" index)
            F.FInt
            (F.PAnd [use (index - 1) (sym "z" index), F.EEq (var (sym "z" index)) (var (sym "y" index))])
        ]
    formals = [binding (1000 + index) (sym "v" index) F.FInt F.PTrue | index <- [0 .. depth]]
    bindings = F.bindEnvFromList (base ++ concatMap step [1 .. depth] ++ formals ++ [binding 200 "x" F.FInt (use depth "x")])
    cube index =
        Sol.Cube
            (F.fromListIBindEnv (if index == 0 then [1] else [2 * index, 2 * index + 1]))
            (F.mkSubst [(sym "v" index, var (sym "y" index))])
            (fromIntegral index)
            []
    solution =
        Sol.Sol
            mempty
            (M.fromList [(kvar index, [cube index]) | index <- [0 .. depth]])
            (M.fromList [(kvar index, F.emptyIBindEnv) | index <- [0 .. depth]])
    constraint = F.SimpC (F.fromListIBindEnv [200]) (F.EEq (var "x") (int target)) (Just 99) 200 [] ()

diamondQuery :: Int -> Integer -> F.FInfo ()
diamondQuery depth target =
    mempty
        { F.bs = bindings
        , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- constraints]
        , F.ws = M.fromList [(kvar index, F.WfC F.emptyIBindEnv [(sym "v" index, F.FInt)] (kvar index) ()) | index <- [0 .. depth]]
        , F.ae = mempty{F.aenvNative = Just S.empty}
        }
  where
    (info, solution, final) = diamond depth target
    bindings = F.bs info
    constraints =
        [ mkConstraint (Sol.cuId cube + 1) (Sol.cuBinds cube) F.FInt F.PTrue (F.PKVar key mempty (F.toKVarSubst substitutions))
        | (key, cubes) <- M.toList (Sol.sHyp solution)
        , cube <- cubes
        , let F.Su substitutions = Sol.cuSubst cube
        ]
            ++ [mkConstraint 99 (F.senv final) F.FInt F.PTrue (F.crhs final)]

capture :: Integer -> Fixture
capture value = (info, solution, constraint)
  where
    info = mempty{F.bs = bindings, F.ws = M.singleton (kvar 0) (F.WfC mempty [("v0", F.FInt)] (kvar 0) ())}
    bindings =
        F.bindEnvFromList
            [ binding 0 "y" F.FInt (F.EEq (var "y") (int 0))
            , binding 1 "v0" F.FInt F.PTrue
            , binding 2 "y" F.FInt (F.PAnd [F.EEq (var "y") (int value), use 0 "y"])
            ]
    cube = Sol.Cube (F.fromListIBindEnv [0]) (F.mkSubst [("v0", var "y")]) 0 []
    solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) F.emptyIBindEnv)
    constraint = F.SimpC (F.fromListIBindEnv [2]) F.PFalse (Just 99) 2 [] ()

poly :: F.Sort -> Bool -> Fixture
poly sort nested = (info, solution, constraint)
  where
    info = mempty{F.bs = bindings, F.ws = M.fromList [(kvar index, F.WfC mempty [("vv", F.boolSort)] (kvar index) ()) | index <- [0, 1]]}
    three = F.PAnd [F.PAtom F.Ne (var "a") (var "b"), F.PAtom F.Ne (var "a") (var "c"), F.PAtom F.Ne (var "b") (var "c")]
    leaf = F.PKVar (kvar 0) mempty mempty
    top = F.PKVar (kvar (if nested then 1 else 0)) (M.singleton "element" sort) mempty
    bindings =
        F.bindEnvFromList
            [ binding 0 "a" (F.FObj "element") three
            , binding 1 "b" (F.FObj "element") F.PTrue
            , binding 2 "c" (F.FObj "element") F.PTrue
            , binding 3 "wrapper" F.boolSort leaf
            , binding 4 "target" F.boolSort top
            ]
    cube0 = Sol.Cube (F.fromListIBindEnv [0, 1, 2]) mempty 0 []
    cube1 = Sol.Cube (F.fromListIBindEnv [3]) mempty 1 []
    solution =
        Sol.Sol
            mempty
            (M.fromList [(kvar 0, [cube0]), (kvar 1, [cube1])])
            (M.fromList [(kvar 0, F.emptyIBindEnv), (kvar 1, F.emptyIBindEnv)])
    constraint = F.SimpC (F.fromListIBindEnv [4]) F.PFalse (Just 99) 4 [] ()

globalActual :: Bool -> Fixture
globalActual present = (info, solution, constraint)
  where
    info = mempty{F.bs = bindings, F.ws = M.fromList [(kvar 0, F.WfC mempty [("vv", F.boolSort)] (kvar 0) ()), (kvar 1, F.WfC mempty [("flag", F.boolSort)] (kvar 1) ())]}
    inner = F.PKVar (kvar 0) mempty mempty
    outer = F.PKVar (kvar 1) mempty (F.toKVarSubst (M.singleton "flag" inner))
    bindings =
        F.bindEnvFromList $
            [ binding 0 "dummy" F.boolSort (F.EEq (var "ghost") (int 0))
            , binding 1 "flag" F.boolSort F.PTrue
            , binding 2 "local" F.boolSort (var "local")
            , binding 3 "target" F.boolSort outer
            ]
                ++ [binding 4 "ghost" F.FInt (F.EEq (var "ghost") (int 0)) | present]
    leaf = Sol.Cube (F.fromListIBindEnv [0]) mempty 0 []
    outerCube = Sol.Cube (F.fromListIBindEnv [2]) (F.mkSubst [("flag", var "local")]) 1 []
    solution =
        Sol.Sol
            mempty
            (M.fromList [(kvar 0, [leaf]), (kvar 1, [outerCube])])
            (M.fromList [(kvar 0, mempty), (kvar 1, mempty)])
    constraint = F.SimpC (F.fromListIBindEnv ([3] ++ [4 | present])) (var "flag") (Just 99) 3 [] ()

multiCubeActual :: Bool -> Fixture
multiCubeActual present = (info{F.bs = bindings'}, solution', constraint)
  where
    (info, solution, constraint) = globalActual present
    bindings = F.bs info
    bindings' = F.bindEnvFromList (binding 5 "second" F.boolSort (var "second") : F.bindEnvToList bindings)
    cube = Sol.Cube (F.fromListIBindEnv [5]) (F.mkSubst [("flag", var "second")]) 2 []
    solution' = solution{Sol.sHyp = M.adjust (++ [cube]) (kvar 1) (Sol.sHyp solution)}

-- The cube means exists x:Bool. x = defined && formal = (x = True).
-- Its existential owns x in both its predicate and defining substitution;
-- the unrelated outer x:Int must not make that substitution ill-sorted.
cubeBinderOwnership :: Bool -> Bool -> Fixture
cubeBinderOwnership defined actual = (info, solution, constraint)
  where
    info = mempty{F.bs = bindings, F.ws = M.singleton (kvar 0) (F.WfC mempty [("formal", F.boolSort)] (kvar 0) ())}
    boolean value = if value then F.PTrue else F.PFalse
    occurrence = F.PKVar (kvar 0) mempty (F.mkKVarSubst [("formal", boolean actual)])
    bindings =
        F.bindEnvFromList
            [ binding 0 "x" F.boolSort (F.EEq (var "x") (boolean defined))
            , binding 1 "formal" F.boolSort F.PTrue
            , binding 2 "target" F.boolSort (F.PAll [("x", F.FInt)] occurrence)
            ]
    cube = Sol.Cube (F.fromListIBindEnv [0]) (F.mkSubst [("formal", F.EEq (var "x") F.PTrue)]) 0 []
    solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) mempty)
    constraint = F.SimpC (F.fromListIBindEnv [2]) F.PFalse (Just 99) 2 [] ()

-- The source binder belongs to every occurrence's context, but not to the
-- exported interface. The result must still equal input + the fixed global.
exportedSolution :: Bool -> Assertion
exportedSolution duplicate = do
    (_, _, prepared, _) <- Solver.simplifyFInfo config query
    let solution = Graph.siSol (Eliminate.solverInfo config prepared)
        sourceScope = M.lookupDefault mempty (kvar 0) (Sol.sScp solution)
        formals = F.kvarDomain prepared (kvar 0)
        sourceNames = [name | (name, _) <- F.envCs (F.bs prepared) sourceScope]
    assertBool "the internal common scope retains the source binder" (F.memberIBindEnv 0 sourceScope)
    assertBool "uniquified formals are not source witnesses" (all (`notElem` sourceNames) formals)
    result <- Solver.solve config query
    case F.resStatus result of
        F.Safe _ -> pure ()
        status -> assertFailure ("identity relation was rejected: " ++ show status)
    case M.lookup (kvar 0) (F.resNonCutsSolution result) of
        Nothing -> assertFailure "expected an eliminated public solution"
        Just delayed -> do
            let predicate = F.forceDelayed delayed
                formal name = M.fromList [(F.formalSource f, F.formalCanonical f) | f <- F.resScopes result M.! kvar 0] M.! name
                expected = F.EEq (var (formal "vv")) (F.EBin F.Plus (var (formal "input")) (var "fixed"))
                theory = So.theoryEnv config (mempty :: F.SInfo ())
                declarations = F.fromListSEnv [(name, F.FInt) | name <- [formal "vv", formal "input", "fixed"]]
                environment = F.symEnv config (declarations <> (F.tsSort <$> theory)) theory [] mempty
            F.syms predicate @?= S.fromList [formal "vv", formal "input", "fixed"]
            equivalent <- withSMT (SMT.makeContextWithSEnv config "exported-solution" environment mempty) $ do
                SMT.smtAssert (So.elaborateExpr (C.solverFlags config) environment mempty "exported relation" (F.PNot (F.PIff predicate expected)) (Just F.boolSort))
                SMT.smtCheckUnsat
            assertBool "the exported relation is exactly input + fixed" equivalent
  where
    config = cfg{C.eliminate = C.Some, C.cores = Just 1, C.noEnvReduction = True}
    context = F.fromListIBindEnv ([0] ++ [2 | duplicate])
    occurrence = F.PKVar (kvar 0) mempty (F.mkKVarSubst [("input", var "source")])
    relation = F.EEq (var "vv") (F.EBin F.Plus (var "source") (var "fixed"))
    constraints = [mkConstraint 1 context F.FInt relation occurrence, mkConstraint 2 context F.FInt occurrence relation]
    query =
        mempty
            { F.bs = F.bindEnvFromList ([binding 0 "source" F.FInt F.PTrue, binding 1 "input" F.FInt F.PTrue] ++ [binding 2 "fixed" F.FInt F.PTrue | duplicate])
            , F.gLits = F.fromListSEnv [("fixed", F.FInt)]
            , F.hoInfo = F.cfgHoInfo config
            , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- constraints]
            , F.ws = M.singleton (kvar 0) (F.WfC (F.fromListIBindEnv [1]) [("vv", F.FInt)] (kvar 0) ())
            }

declaredGlobalShadow :: Bool -> Assertion
declaredGlobalShadow declared =
    forM_ [(F.PAll, True), (F.PExist, False)] $ \(quantifier, expected) -> do
        let occurrence = F.PKVar (kvar 0) mempty (F.mkKVarSubst [("formal", var "fixed")])
            bindings =
                F.bindEnvFromList
                    [ binding 0 "witness" F.FInt (F.EEq (var "witness") (var "fixed"))
                    , binding 1 "formal" F.FInt F.PTrue
                    , binding 2 "target" F.boolSort (quantifier [("fixed", F.FInt)] occurrence)
                    , binding 3 "fixed" F.FInt F.PTrue
                    ]
            info = mempty{F.bs = bindings, F.gLits = F.fromListSEnv [("fixed", F.FInt) | declared], F.ws = M.singleton (kvar 0) (F.WfC mempty [("formal", F.FInt)] (kvar 0) ())}
            cube = Sol.Cube (F.fromListIBindEnv [0, 3]) (F.mkSubst [("formal", var "witness")]) 0 []
            solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) (F.fromListIBindEnv [3]))
            constraint = F.SimpC (F.fromListIBindEnv [2, 3]) F.PFalse (Just 99) 2 [] ()
            scope = S.fromList ["witness", "formal", "target", "fixed"]
            initial = Solution.prepareSummaryState scope info
            (definitions, predicate) = Solution.lhsPredShared cfg initial scope mempty info solution constraint
            original = Solution.lhsPred cfg scope mempty info solution constraint
        -- The actual follows the consumer binder; the definition retains its
        -- global or common-context name. Forall is false; exists is satisfiable.
        mapM_ (\(equations, body) -> valid (info, solution, constraint) equations body >>= (@?= expected)) [(definitions, predicate), ([], original)]

normalizedFormals :: Assertion
normalizedFormals = do
    (_, _, prepared, _) <- Solver.simplifyFInfo cfg query
    let declared = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList (F.bs prepared)]
        expressions =
            map F.crhs (M.elems (F.cm prepared))
                ++ [F.reftPred (F.sr_reft refinement) | (_, (_, refinement, _)) <- F.bindEnvToList (F.bs prepared)]
        domains = S.unions (map (V.fold folder () mempty) expressions)
    assertBool "the control retains actual KVar arguments" (not (S.null domains))
    assertBool "every surviving formal owns a typed BindEnv row" (domains `S.isSubsetOf` declared)
    assertBool
        "native/global names outside the WF domain are not formals"
        (all (not . (`S.member` domains)) ["bool_to_int", "ghost", "Set_cup"])
  where
    query = V.mapKVarSubsts add (diamondQuery 1 0)
    add _ substitution =
        F.toKVarSubst $
            M.fromList [("bool_to_int", var "bool_to_int"), ("ghost", int 1), ("Set_cup", var "Set_cap")]
                <> F.fromKVarSubst substitution
    folder :: V.Folder (S.HashSet F.Symbol) ()
    folder = (V.defaultFolder :: V.Folder (S.HashSet F.Symbol) ()){V.accExpr = arguments}
    arguments _ (F.PKVar _ _ substitution) = S.fromList (M.keys (F.fromKVarSubst substitution))
    arguments _ _ = mempty

numericAliasElimination :: C.Eliminate -> Integer -> Assertion
numericAliasElimination mode value = do
    (_, _, prepared, _) <- Solver.simplifyFInfo config query
    let solution = Graph.siSol (Eliminate.solverInfo config prepared)
        targets = [constraint | constraint <- M.elems (F.cm prepared), F.crhs constraint == F.PFalse]
        bindings = F.bs prepared
        scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList bindings]
    assertBool "the real KVar is eliminated, not approximated by qualifiers" (not (M.null (Sol.sHyp solution)))
    case targets of
        [target] -> do
            let initial = Solution.prepareSummaryState scope prepared
                (definitions, _) = Solution.lhsPredShared config initial scope mempty prepared solution target
                exports = Solution.nonCutsResult config scope prepared solution
                replace (F.PKVar key types actuals) =
                    F.subst (F.Su (F.fromKVarSubst actuals)) (V.applyCoSub types (F.forceDelayed (exports M.! key)))
                replace expression = expression
                exported =
                    V.trans replace $
                        F.pAnd
                            [ F.subst1 (F.reftPred (F.sr_reft refinement)) (F.reftBind (F.sr_reft refinement), var name)
                            | index <- F.elemsIBindEnv (F.senv target)
                            , let (name, refinement, _) = F.lookupBindEnv index bindings
                            ]
                original = Solution.lhsPred config scope mempty prepared solution target
            assertBool "the normalized occurrence produces a hoisted summary" (not (null definitions))
            assertBool "the summary retains a Real formal" (any (any ((== F.FReal) . snd) . F.eqArgs) definitions)
            V.kvarsExpr exported @?= []
            equivalent <- valid (prepared, solution, target{F._crhs = F.PFalse}) [] (elaboratedExport prepared (F.PNot (F.PIff exported original)))
            assertBool "closed export retains normalized annotation ownership under shadowing" equivalent
            check "numeric alias after actual normalization" (value == 1) True (prepared, solution, target)
        _ -> assertFailure "expected exactly one concrete target after normalization"
    result <- Solver.solve config query
    case (value, F.resStatus result) of
        (1, F.Safe _) -> pure ()
        (0, F.Unsafe _ _) -> pure ()
        _ -> assertFailure ("unexpected numeric alias result: " ++ show (F.resStatus result))
  where
    config = cfg{C.eliminate = mode, C.cores = Just 1, C.noEnvReduction = True}
    query = numericAliasQuery value

numericAliasQuery :: Integer -> F.FInfo ()
-- An inner integral value does not shadow the ambient fractional type alias.
-- The KVar's explicit actual annotation retains that declaration's ownership.
-- Half-integer witnesses require Real, and offset zero remains satisfiable.
numericAliasQuery value =
    mempty
        { F.bs = F.bindEnvFromList [binding 0 "alpha" F.FFrac F.PTrue]
        , F.hoInfo = F.cfgHoInfo cfg
        , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- [definition, target]]
        , F.ws = M.singleton (kvar 0) (F.WfC mempty [("vv", F.FReal)] (kvar 0) ())
        }
  where
    occurrence actual = F.PKVar (kvar 0) mempty (F.toKVarSubst (M.singleton "vv" actual))
    definition = mkConstraint 1 mempty F.FReal (F.EEq (var "vv") (F.ECon (F.R (1 / 2)))) (occurrence (var "vv"))
    target =
        mkConstraint
            2
            (F.fromListIBindEnv [0])
            F.boolSort
            ( F.PExist
                [("alpha", F.FInt), ("local", F.FObj "alpha")]
                (F.PAnd [F.EEq (var "local") (F.ECon (F.R (fromInteger value + 1 / 2))), occurrence (F.ECst (var "local") (F.FObj "alpha"))])
            )
            F.PFalse

globalElimination :: F.Symbol -> F.FInfo () -> C.Eliminate -> F.Brel -> Assertion
globalElimination name query mode relation = do
    (parameter, _, prepared, _) <- Solver.simplifyFInfo config query
    let environment = So.epEnv parameter
        solution = Graph.siSol (Eliminate.solverInfo config prepared)
        bindings = F.bs prepared
        scope = S.fromList (map fst (F.toListSEnv (F.seSort environment)))
        targets = [constraint | constraint <- M.elems (F.cm prepared), F.crhs constraint == F.PFalse]
    assertBool "the global declaration also has a BindEnv row" (any ((== name) . firstName) (F.bindEnvToList bindings))
    case targets of
        [target] -> do
            let initial = Solution.prepareSummaryState scope prepared
                (definitions, predicate) = Solution.lhsPredShared config initial scope mempty prepared solution target
                original = Solution.lhsPred config scope mempty prepared solution target
                expected = relation == F.Ne
            assertBool "an eliminated summary is required" (not (null definitions))
            assertBool "a fixed global became a summary parameter" (all (all ((/= name) . fst) . F.eqArgs) definitions)
            mapM_ (\(equations, body) -> observe environment equations body >>= (@?= expected)) [(definitions, predicate), ([], original)]
        _ -> assertFailure "expected one concrete global target"
    result <- Solver.solve config query
    case (relation, F.resStatus result) of
        (F.Ne, F.Safe _) -> pure ()
        (F.Eq, F.Unsafe _ _) -> pure ()
        _ -> assertFailure ("unexpected global result: " ++ show (F.resStatus result))
  where
    config = cfg{C.eliminate = mode, C.cores = Just 1, C.noEnvReduction = True}
    firstName (_, (symbol, _, _)) = symbol
    observe environment equations body =
        withSMT (SMT.makeContextWithSEnv config "native-summary" environment mempty) $ do
            forM_ equations $ \equation -> SMT.smtDefineFunc (F.eqName equation) (F.eqArgs equation) (F.eqSort equation) (F.eqBody equation)
            SMT.smtAssert body
            SMT.smtCheckUnsat

nativeGlobalQuery :: Bool -> Int -> F.Brel -> F.FInfo ()
nativeGlobalQuery common shape relation =
    mempty
        { F.bs = F.bindEnvFromList [binding 0 "Method" scheme F.PTrue, binding 1 "ints" (F.FFunc F.FInt F.boolSort) F.PTrue, binding 2 "bools" (F.FFunc F.boolSort F.boolSort) F.PTrue]
        , F.ddecls = [declaration]
        , F.hoInfo = F.cfgHoInfo cfg
        , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- [definition, target]]
        , F.ws = M.singleton (kvar 0) (F.WfC mempty [("vv", F.boolSort)] (kvar 0) ())
        }
  where
    tycon = F.symbolFTycon (F.dummyLoc "Method")
    method sort = F.FApp (F.FTC tycon) sort
    constructor sort = F.FFunc (F.FFunc sort F.boolSort) (F.FFunc F.FInt (method sort))
    scheme = F.FAbs 0 (constructor (F.FVar 0))
    declaration = F.DDecl tycon 1 [F.DCtor (F.dummyLoc "Method") [F.DField (F.dummyLoc "callback") (F.FFunc (F.FVar 0) F.boolSort), F.DField (F.dummyLoc "marker") F.FInt]]
    record sort callback = case shape of
        0 -> F.eApps (var "Method") [var callback, int 0]
        1 -> F.ELet "partial" (F.EApp (var "Method") (var callback)) (F.EApp (var "partial") (int 0))
        _ -> F.ELet "builder" (F.ECst (var "Method") (constructor sort)) (F.eApps (var "builder") [var callback, int 0])
    predicate = F.PAnd [F.PAtom relation (F.EApp (var "callback") (record sort name)) (var name) | (sort, name) <- [(F.FInt, "ints"), (F.boolSort, "bools")]]
    occurrence = F.PKVar (kvar 0) mempty mempty
    context = F.fromListIBindEnv [0, 1, 2]
    definition = mkConstraint 1 context F.boolSort predicate occurrence
    target = mkConstraint 2 (if common then context else F.deleteIBindEnv 0 context) F.boolSort occurrence F.PFalse

-- The global is a family of values, not one term at its default Int instance.
-- A summary must preserve its cast to Cell Token rather than capture the scheme.
polymorphicGlobalQuery :: Bool -> F.Brel -> F.FInfo ()
polymorphicGlobalQuery common relation =
    mempty
        { F.bs = F.bindEnvFromList [binding 0 "empty" scheme F.PTrue, binding 1 "witness" carrier F.PTrue]
        , F.gLits = F.fromListSEnv [("empty", scheme)]
        , F.ddecls = [F.DDecl cell 1 [F.DCtor (F.dummyLoc "Cell") [F.DField (F.dummyLoc "payload") (F.FVar 0)]], F.DDecl token 0 [F.DCtor (F.dummyLoc "Token") []]]
        , F.hoInfo = F.cfgHoInfo cfg
        , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- [definition, target]]
        , F.ws = M.singleton (kvar 0) (F.WfC mempty [("vv", F.boolSort)] (kvar 0) ())
        }
  where
    cell = F.symbolFTycon (F.dummyLoc "Cell")
    token = F.symbolFTycon (F.dummyLoc "Token")
    scheme = F.FAbs 0 (F.FApp (F.FTC cell) (F.FVar 0))
    carrier = F.FApp (F.FTC cell) (F.FTC token)
    selected = F.ECst (var "empty") carrier
    occurrence = F.PKVar (kvar 0) mempty mempty
    context = F.fromListIBindEnv [0, 1]
    definition = mkConstraint 1 context F.boolSort (F.EEq (var "witness") selected) occurrence
    target = mkConstraint 2 (if common then context else F.deleteIBindEnv 0 context) F.boolSort (F.PAnd [occurrence, F.PAtom relation (var "witness") selected]) F.PFalse

nativeFunctionQuery :: Integer -> F.FInfo ()
nativeFunctionQuery value =
    mempty
        { F.bs = F.bindEnvFromList [binding 0 "function" (F.FFunc F.boolSort F.FInt) F.PTrue]
        , F.hoInfo = F.cfgHoInfo cfg
        , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- [definition, target]]
        , F.ws = M.singleton (kvar 0) (F.WfC (F.fromListIBindEnv [0]) [("vv", F.boolSort)] (kvar 0) ())
        , F.ae = mempty{F.aenvNative = Just S.empty}
        }
  where
    occurrence actual = F.PKVar (kvar 0) mempty (F.toKVarSubst (M.singleton "function" actual))
    definition = mkConstraint 1 (F.fromListIBindEnv [0]) F.boolSort (F.EEq (F.EApp (var "function") F.PTrue) (int value)) (occurrence (var "function"))
    target = mkConstraint 2 mempty F.boolSort (occurrence (var "bool_to_int")) F.PFalse

-- The inner KVar retains the surrounding function in its common scope, but
-- the outer cube existentially owns it. Hoisting the inner predicate must not
-- replace that function with the native declaration of the same spelling.
cubeLocalFunction :: F.Symbol -> C.Eliminate -> Integer -> Assertion
cubeLocalFunction name mode value = do
    (parameter, _, prepared, _) <- Solver.simplifyFInfo config query
    let environment = So.epEnv parameter
        solution = Graph.siSol (Eliminate.solverInfo config prepared)
        bindings = F.bs prepared
        expressions =
            map F.crhs (M.elems (F.cm prepared))
                ++ [F.reftPred (F.sr_reft refinement) | (_, (_, refinement, _)) <- F.bindEnvToList bindings]
        scope =
            S.unions
                [ S.fromList (map fst (F.toListSEnv (F.seSort environment)))
                , S.fromList [symbol | (_, (symbol, _, _)) <- F.bindEnvToList bindings]
                , foldMap (foldMap S.singleton) expressions
                ]
        targets = [constraint | constraint <- M.elems (F.cm prepared), F.crhs constraint == F.PFalse]
        (functionName, functionRefinement, _) = F.lookupBindEnv 0 bindings
        ownsFunction cube =
            F.memberIBindEnv 0 (Sol.cuBinds cube)
                && not (F.memberIBindEnv 0 (M.lookupDefault mempty (kvar 1) (Sol.sScp solution)))
    fmap F.tsSort (F.lookupSEnv "bool_to_int" (F.seTheory environment)) @?= Just functionSort
    (functionName, F.sr_sort functionRefinement) @?= (name, functionSort)
    assertBool "both KVars eliminate" (all (`M.member` Sol.sHyp solution) [kvar 0, kvar 1])
    assertBool "the inner common scope retains the function" (F.memberIBindEnv 0 (M.lookupDefault mempty (kvar 0) (Sol.sScp solution)))
    assertBool "the outer cube existentially owns the function" (any ownsFunction (M.lookupDefault [] (kvar 1) (Sol.sHyp solution)))
    case targets of
        [target] -> do
            let initial = Solution.prepareSummaryState scope prepared
                (definitions, predicate) = Solution.lhsPredShared config initial scope mempty prepared solution target
                original = Solution.lhsPred config scope mempty prepared solution target
            assertBool "the test exercises hoisted definitions" (not (null definitions))
            -- A function mapping True to either zero or one exists. The
            -- native bool_to_int maps True only to one, so zero distinguishes
            -- accidental global lookup from the source existential witness.
            observe environment [] original >>= assertEqual "expanded existential remains satisfiable" SMT.Sat
            observe environment definitions predicate >>= assertEqual "shared existential remains satisfiable" SMT.Sat
        _ -> assertFailure "expected one concrete cube-local target"
  where
    config = cfg{C.eliminate = mode, C.cores = Just 1, C.noEnvReduction = True}
    functionSort = F.FFunc F.boolSort F.FInt
    context = F.fromListIBindEnv [0]
    inner = F.PKVar (kvar 0) mempty mempty
    outer = F.PKVar (kvar 1) mempty mempty
    constraints =
        [ mkConstraint 1 context F.boolSort F.PTrue inner
        , mkConstraint 2 context F.boolSort inner outer
        , mkConstraint 3 mempty F.boolSort outer F.PFalse
        ]
    query =
        mempty
            { F.bs = F.bindEnvFromList [binding 0 name functionSort (F.EEq (F.EApp (var name) F.PTrue) (int value))]
            , F.hoInfo = F.cfgHoInfo cfg
            , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- constraints]
            , F.ws = M.fromList [(kvar 0, F.WfC context [("vv", F.boolSort)] (kvar 0) ()), (kvar 1, F.WfC mempty [("vv", F.boolSort)] (kvar 1) ())]
            , F.ae = mempty{F.aenvNative = Just S.empty}
            }
    observe environment equations body =
        withSMT (SMT.makeContextWithSEnv config "cube-local-function" environment mempty) $ do
            forM_ equations $ \equation -> SMT.smtDefineFunc (F.eqName equation) (F.eqArgs equation) (F.eqSort equation) (F.eqBody equation)
            SMT.smtAssert body
            SMT.command SMT.CheckSat

indexedDefinitionResult :: C.Eliminate -> Bool -> Assertion
indexedDefinitionResult mode conclusion = do
    result <- Solver.solve cfg{C.eliminate = mode, C.cores = Just 1} (indexedDefinitionQuery True conclusion)
    case (conclusion, F.resStatus result) of
        (True, F.Safe _) -> pure ()
        (False, F.Unsafe _ owners) -> map fst owners @?= [2]
        _ -> assertFailure ("unexpected indexed definition result: " ++ show (F.resStatus result))

indexedDefinitionCut :: Bool -> Assertion
indexedDefinitionCut instantiated = do
    (_, _, prepared, _) <- Solver.simplifyFInfo config (indexedDefinitionQuery instantiated False)
    let (_, dependencies) = Graph.elimVars config prepared
    S.member (kvar 0) (Graph.depCuts dependencies) @?= instantiated
    S.member (kvar 0) (Graph.depNonCuts dependencies) @?= not instantiated
    assertBool "an unrelated KVar still eliminates" (S.member (kvar 1) (Graph.depNonCuts dependencies))
  where
    config = cfg{C.eliminate = C.Some, C.cores = Just 1}

-- The defining occurrence constrains only K[output := Authority], whereas
-- the consumer retains the abstract output index. A Cube cannot forget that
-- substitution and equate Fields Int Authority with Fields Int Int. Keeping
-- this definition in qualifier inference is conservative, not polymorphic
-- elimination. An explicit identity substitution needs no such cut.
indexedDefinitionQuery :: Bool -> Bool -> F.FInfo ()
indexedDefinitionQuery instantiated conclusion =
    mempty
        { F.bs =
            F.bindEnvFromList
                [ binding 0 "formal" (fields abstract) F.PTrue
                , binding 1 "x" (fields defined) definitionPredicate
                , binding 2 "y" (fields abstract) F.PTrue
                ]
        , F.ddecls = [fieldsDeclaration, authorityDeclaration]
        , F.hoInfo = F.cfgHoInfo cfg
        , F.cm = M.fromList [(F.subcId constraint, constraint) | constraint <- constraints]
        , F.ws =
            M.fromList
                [ (kvar 0, F.WfC (F.fromListIBindEnv [0]) [("vv", F.boolSort)] (kvar 0) ())
                , (kvar 1, F.WfC mempty [("vv", F.FInt)] (kvar 1) ())
                ]
        }
  where
    authorityTycon = F.symbolFTycon (F.dummyLoc "Authority")
    authority = F.FTC authorityTycon
    authorityDeclaration = F.DDecl authorityTycon 0 [F.DCtor (F.dummyLoc "Ordinary") [], F.DCtor (F.dummyLoc "Override") []]
    fieldsTycon = F.symbolFTycon (F.dummyLoc "Fields")
    fields output = F.FApp (F.FApp (F.FTC fieldsTycon) F.FInt) output
    -- The indices occur underneath function carriers, as in a parser schema.
    fieldsDeclaration =
        F.DDecl
            fieldsTycon
            2
            [ F.DCtor
                (F.dummyLoc "Fields")
                [ F.DField (F.dummyLoc "field") (F.FFunc F.FInt (F.FVar 1))
                , F.DField (F.dummyLoc "encode") (F.FFunc (F.FVar 0) F.FInt)
                ]
            ]
    abstract = F.FObj "output"
    defined = if instantiated then authority else abstract
    definitionPredicate
        | instantiated = F.EEq (F.EApp (F.EApp (var "field") (var "x")) (int 0)) (var "Ordinary")
        | otherwise = F.PTrue
    occurrence types actual = F.PKVar (kvar 0) types (F.toKVarSubst (M.singleton "formal" (var actual)))
    independent = F.PKVar (kvar 1) mempty mempty
    zero = F.EEq (var "vv") (int 0)
    constraints =
        [ mkConstraint 1 (F.fromListIBindEnv [1]) F.boolSort F.PTrue (occurrence (M.singleton "output" defined) "x")
        , mkConstraint 2 (F.fromListIBindEnv [2]) F.boolSort (occurrence mempty "y") (if conclusion then F.PTrue else F.PFalse)
        , mkConstraint 3 mempty F.FInt zero independent
        , mkConstraint 4 mempty F.FInt independent zero
        ]

mkConstraint :: Integer -> F.IBindEnv -> F.Sort -> F.Expr -> F.Expr -> F.SubC ()
mkConstraint index context sort lhs rhs = F.mkSubC context (refinement lhs) (refinement rhs) (Just index) [] ()
  where
    refinement predicate = F.RR sort (F.Reft ("vv", predicate))

withUnknownGlobal :: F.FInfo () -> F.FInfo ()
withUnknownGlobal query = query{F.bs = F.bindEnvFromList (map replace (F.bindEnvToList (F.bs query)))}
  where
    replace (1, (name, refinement, annotation)) =
        (1, (name, refinement{F.sr_reft = F.Reft (name, F.EEq (var "ghost") (int 0))}, annotation))
    replace binding' = binding'

diamondActual :: Int -> Integer -> Fixture
diamondActual depth target = (info, solution, constraint)
  where
    (originalInfo, originalSolution, _) = diamond depth target
    originalBindings = F.bs originalInfo
    info = originalInfo{F.bs = bindings, F.ws = M.insert outerKey (F.WfC mempty [("flag", F.boolSort)] (outerKey) ()) (F.ws originalInfo)}
    inner = use depth "x"
    outerKey = kvar (depth + 1)
    outer = F.PKVar outerKey mempty (F.toKVarSubst (M.singleton "flag" inner))
    bindings =
        F.bindEnvFromList $
            filter ((/= 200) . fst) (F.bindEnvToList originalBindings)
                ++ [ binding 200 "x" F.FInt F.PTrue
                   , binding 300 "flag" F.boolSort F.PTrue
                   , binding 301 "local" F.boolSort (var "local")
                   , binding 302 "target" F.boolSort outer
                   ]
    cube = Sol.Cube (F.fromListIBindEnv [301]) (F.mkSubst [("flag", var "local")]) 100 []
    solution =
        originalSolution
            { Sol.sHyp = M.insert outerKey [cube] (Sol.sHyp originalSolution)
            , Sol.sScp = M.insert outerKey mempty (Sol.sScp originalSolution)
            }
    constraint = F.SimpC (F.fromListIBindEnv [200, 302]) (F.EEq (var "x") (int target)) (Just 99) 302 [] ()

-- Constructor identity does not identify a source-admission judgment. These
-- actuals start well-sorted under their declaration, but specialization changes
-- numeric evidence. Reusing the first specialized body must not change whether
-- the next actual is admitted, in either observation order.
specializedCapabilityAdmission :: Bool -> Assertion
specializedCapabilityAdmission numericFirst = do
    let declarations = F.fromListSEnv [("element", F.FNum), ("a", F.FInt)]
        admitted = So.sortExprE Nothing F.dummySpan declarations mempty actual
    assertBool "original actual must be admitted under its numeric declaration" (either (const False) (== F.boolSort) admitted)
    direct <- valid fixture [] (Solution.lhsPred cfg scope mempty info solution constraint)
    shared <- valid fixture definitions predicate
    assertEqual "direct reconstruction has the independently expected verdict" numericFirst direct
    assertEqual "specialization sharing preserves actual admission" direct shared
  where
    numeric = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc "NumericWitness") True False)
    opaque = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc "NumericWitness") False False)
    actual = F.EEq (F.ECst (F.ENeg (var "a")) (F.FObj "element")) (int 0)
    occurrence selected = F.PKVar (kvar 1) mempty (F.mkKVarSubst [("formal1", F.PKVar (kvar 0) (M.singleton "element" selected) mempty)])
    combination
        | numericFirst = F.PAnd [occurrence numeric, occurrence opaque]
        | otherwise = F.POr [occurrence opaque, occurrence numeric]
    bindings =
        F.bindEnvFromList
            [ binding 0 "element" F.FNum F.PTrue
            , binding 1 "formal0" F.boolSort (var "formal0")
            , binding 2 "formal1" F.boolSort (F.PNot (var "formal1"))
            , binding 3 "a" F.FInt F.PTrue
            , binding 4 "b" F.boolSort (var "b")
            , binding 5 "target" F.boolSort combination
            ]
    info =
        mempty
            { F.bs = bindings
            , F.ws =
                M.fromList
                    [ (kvar 0, F.WfC mempty [("formal0", F.boolSort)] (kvar 0) ())
                    , (kvar 1, F.WfC mempty [("formal1", F.boolSort)] (kvar 1) ())
                    ]
            }
    inner = Sol.Cube (F.fromListIBindEnv [3]) (F.mkSubst [("formal0", actual)]) 0 []
    outer = Sol.Cube (F.fromListIBindEnv [4]) (F.mkSubst [("formal1", var "b")]) 1 []
    solution =
        Sol.Sol
            mempty
            (M.fromList [(kvar 0, [inner]), (kvar 1, [outer])])
            (M.fromList [(kvar 0, mempty), (kvar 1, mempty)])
    constraint = F.SimpC (F.fromListIBindEnv [0, 1, 2, 5]) F.PFalse (Just 99) 5 [] ()
    fixture = (info, solution, constraint)
    scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList bindings]
    initial = Solution.prepareSummaryState scope info
    (definitions, predicate) = Solution.lhsPredShared cfg initial scope mempty info solution constraint
