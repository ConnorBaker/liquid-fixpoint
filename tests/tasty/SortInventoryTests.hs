{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module SortInventoryTests (tests, allocationBytes) where

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate)
import Control.Monad.Reader (runReader)
import qualified Data.Generics as G
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.IntMap.Strict as IM
import Data.List (foldl', sortOn)
import Data.Maybe (isNothing)
import qualified Data.Text as T
import GHC.Conc (getAllocationCounter)
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import qualified Language.Fixpoint.Types.Visitor as Vis
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, testCaseInfo, (@?=))

data Envelope = Envelope F.Symbol T.Text String Int [F.Sort] F.Expr
    deriving (G.Data)

tests :: TestTree
tests =
    testGroup
        "complete sort-coordinate inventory"
        [ testGroup
            "source annotation preserves declarations and independent judgments"
            [ testCase "unused shadowed base coordinates remain reserved" $ do
                let base = F.fromListSEnv [("shadow", F.FAbs 97 (F.FVar 98)), ("poly", F.FAbs 42 (F.FFunc F.FInt (F.FVar 42)))]
                    local = F.fromListSEnv [("shadow", F.boolSort)]
                    result = C.annotateExprEAt flags (Just F.emptySymEnv{F.seSort = base}) local "shadow inventory" Nothing (F.EApp (F.EVar "poly") (F.ECon (F.I 1)))
                case result of
                    Left failure -> assertBool (show failure) False
                    Right expression -> do
                        assertBool "fresh result coordinate missing" (not (S.null (C.sortFieldIndices expression)))
                        S.intersection (C.sortFieldIndices (base, local)) (C.sortFieldIndices expression) @?= S.empty
            , testCase "local declarations shadow base lookup" $ do
                let base = F.fromListSEnv [("value", F.FInt)]
                    local = F.fromListSEnv [("value", F.boolSort)]
                C.annotateExprEAt flags (Just F.emptySymEnv{F.seSort = base}) local "local precedence" (Just F.boolSort) (F.EVar "value")
                    @?= C.annotateExprEAt flags Nothing local "local precedence" (Just F.boolSort) (F.EVar "value")
            , testCase "independent instances use fresh judgment substitutions" $ do
                let bindings = F.fromListSEnv [("id", F.FAbs 42 (F.FFunc (F.FVar 42) (F.FVar 42)))]
                    annotate = C.annotateExprEAt flags Nothing bindings "fresh instance" Nothing
                mapM_
                    ( \(argument, expected) ->
                        let expression = F.EApp (F.EVar "id") argument
                         in fmap C.exprSortMaybe (annotate expression)
                                @?= Right (Just expected)
                    )
                    [(F.ECon (F.I 1), F.FInt), (F.PTrue, F.boolSort), (F.ECon (F.I 2), F.FInt)]
            , testCase "configured native carriers do not erase nominal aliases" $ do
                let bindings = F.fromListSEnv [("AliasA", F.boolSort), ("AliasB", F.boolSort), ("x", F.FObj "AliasA"), ("y", F.FObj "AliasB")]
                    native = F.emptySymEnv{F.seSort = bindings}
                    result = C.annotateExprEAt flags (Just native) mempty "nominal aliases" (Just F.boolSort) (F.PAtom F.Eq (F.EVar "x") (F.EVar "y"))
                assertBool "native Boolean encoding erased distinct source owners" (either (const True) (const False) result)
            , testCase "source annotation retains source arithmetic operator" $ do
                let expression = F.EBin F.Div (F.ECon (F.R 1)) (F.ECon (F.R 2))
                case C.annotateExprEAt flags (Just F.emptySymEnv) mempty "source division" Nothing expression of
                    Right result -> case F.dropECst result of
                        F.EBin operator _ _ -> operator @?= F.Div
                        other -> assertBool (show other) False
                    Left failure -> assertBool (show failure) False
            ]
        , testCase "nested forall labels remain reserved, including unused binders" $
            C.sortFieldIndices nested @?= S.fromList [-7, 12, 19, maxBound]
        , testCase "all sort fields agree with independent full generic traversal" $
            C.sortFieldIndices expression @?= reference expression
        , testCase "KVar sort images and actual annotations remain visible" $
            C.sortFieldIndices kvar @?= S.fromList [31, 32, 33, 34]
        , testCase "free sort support does not demand symbol presentation" $ do
            let poisoned = G.gmapT (G.mkT (const (error "unrequested symbol presentation") :: T.Text -> T.Text)) ("payload" :: F.Symbol)
            Vis.exprFreeSortNames (F.EVar poisoned) @?= S.empty
        , testCase "free sort support does not traverse literal spelling" $ do
            let measure count = do
                    let expression :: F.Expr
                        expression = F.ECon (F.L (T.replicate count "x") (F.FObj "literal_type"))
                    _ <- evaluate (force expression)
                    bytes <- allocationBytes (Vis.exprFreeSortNames expression)
                    Vis.exprFreeSortNames expression @?= S.singleton "literal_type"
                    pure bytes
            short <- measure 16
            long <- measure 1000000
            assertBool "sort inventory traversed literal bytes" (long <= 2 * short + 65536)
        , testCase "native scheme coordinates remain visible in the catalog" $
            C.sortFieldIndices catalog @?= reference catalog
        , testCase "complete mixed catalogs agree with the full generic reference" $
            C.sortFieldIndices largeCatalog @?= reference largeCatalog
        , testCase "term and native catalog coordinates remain reserved during elaboration" $ do
            let declarations = largeCatalog{F.seSort = F.insertSEnv "poly" (F.FAbs 2000 (F.FFunc F.FInt (F.FVar 2000))) (F.seSort largeCatalog)}
                parameter = C.ElabParam (Config.solverFlags Config.defConfig) "catalog inventory control" declarations
                result = C.elabExpr parameter Nothing (F.EApp (F.EVar "poly") (F.ECon (F.I 1)))
                occupied = reference (F.seSort declarations, F.seTheory declarations)
                inferred = C.sortFieldIndices result
            assertBool "polymorphic result must have an inferred coordinate" (not (S.null inferred))
            S.intersection occupied inferred @?= S.empty
        , testCase "unrelated metadata and nested products preserve the full inventory" $
            C.sortFieldIndices envelope @?= reference envelope
        , testCase "nominal alias spelling does not masquerade as an indexed coordinate" $
            C.sortFieldIndices (F.FObj "FVar 999") @?= S.empty
        , testCase "closed symbols and text carry no sort coordinates" $
            C.sortFieldIndices ("FAbs 123" :: F.Symbol, "FVar 456" :: T.Text, "FVar 789" :: String) @?= S.empty
        , testCase "long spellings do not cause coordinate-inventory traversal" $ do
            short <- allocation 8
            long <- allocation 1024
            assertBool "atomic spelling length enlarged sort traversal" (long <= 3 * short + 131072)
        , testCase "catalog inventory costs remain proportional to its sort-field fold" $ do
            _ <- evaluate (force largeCatalog)
            semantic <- allocationBytes (foldMap F.sortIndices (F.seSort largeCatalog) `S.union` foldMap (F.sortIndices . F.tsSort) (F.seTheory largeCatalog))
            generic <- allocationBytes (C.sortFieldIndices (F.seSort largeCatalog, F.seTheory largeCatalog))
            assertBool "catalog representation was traversed instead of its sorts" (generic <= 2 * semantic + 131072)
        , testGroup
            "binder-free substitution uses coordinate lookup"
            [ testCase "symbolic" $
                substitutionAllocation
                    (\width -> M.fromList (("selected", F.FInt) : [(F.symbol ("unused" ++ show index), F.FVar index) | index <- [0 .. width]]))
                    F.sortSubst
                    (F.FObj "selected")
                    (F.FObj "absent")
            , testCase "indexed" $
                substitutionAllocation
                    (\width -> IM.fromList ((-1, F.FInt) : [(index, F.FVar (index + 1)) | index <- [0 .. width]]))
                    F.sortSubstVars
                    (F.FVar (-1))
                    (F.FVar (-2))
            ]
        , testCase "irrelevant images do not affect binder freshness" $ do
            F.sortSubst (M.fromList [("a", F.FVar 0), ("unused", F.FVar 1)]) (F.FAbs 0 (F.FObj "a"))
                @?= F.FAbs 1 (F.FVar 0)
            F.sortSubstVars (IM.fromList [(7, F.FVar 0), (99, F.FVar 1)]) (F.FAbs 0 (F.FVar 7))
                @?= F.FAbs 1 (F.FVar 0)
            F.sortSubstVars (IM.singleton 0 F.FInt) (F.FFunc (F.FVar 0) (F.FAbs 0 (F.FVar 0)))
                @?= F.FFunc F.FInt (F.FAbs 0 (F.FVar 0))
        , testCase "simultaneous owner renaming preserves free images and exact forall labels" $ do
            let renaming = M.fromList [("a", "owned"), ("owned", "other")]
                substitution = IM.fromList [(9, F.FFunc (F.FObj "a") (F.FVar 0)), (12, F.FVar 1)]
                source = F.FAbs 0 (F.FFunc (F.FObj "a") (F.FVar 9))
                sorts =
                    [ source
                    , F.FAbs 0 (F.FAbs 1 (F.FFunc (F.FVar 9) (F.FVar 12)))
                    , F.FAbs 9 (F.FFunc (F.FObj "owned") (F.FVar 9))
                    , F.boolSort
                    ]
            map
                (\(names, indices, sort) -> F.substituteSort (F.FObj <$> names) indices sort)
                [(names, indices, sort) | names <- [mempty, renaming], indices <- [mempty, substitution], sort <- sorts]
                @?= [ F.sortSubstVars indices (F.substSort (\name -> F.FObj (M.lookupDefault name name names)) sort)
                    | names <- [mempty, renaming]
                    , indices <- [mempty, substitution]
                    , sort <- sorts
                    ]
            F.substituteSort (F.FObj <$> renaming) substitution source
                @?= F.FAbs 1 (F.FFunc (F.FObj "owned") (F.FFunc (F.FObj "a") (F.FVar 0)))
        , groundInventoryTests
        , testGroup
            "prepared refinement candidates share numeric-name inventory"
            [ testCase (show expected) $ do
                narrow <- checkingAllocation 256 expected
                wide <- checkingAllocation 4096 expected
                assertBool "each candidate traversed the declaration inventory" (wide <= 4 * narrow + 524288)
            | expected <- [Nothing, Just F.boolSort]
            ]
        , testCase "source scoping does not lower unused declarations" $ do
            let firstCheck depth = do
                    let collection = foldr (const F.setSort) F.FInt [1 :: Int .. depth]
                        unused = F.FFunc (F.mapSort F.FInt collection) collection
                        declarations = F.fromListSEnv [(F.symbol ("unused_" ++ show index), unused) | index <- [1 :: Int .. 512]]
                        candidate = F.RR F.FInt (F.Reft ("value", F.PAtom F.Eq (F.EVar "value") (F.ECon (F.I 0))))
                        result = runReader (C.checkSorted Nothing F.dummySpan declarations candidate) (Config.ElabFlags True False)
                    _ <- evaluate (force (declarations, candidate))
                    bytes <- allocationBytes (fmap show result)
                    fmap show result @?= Nothing
                    pure bytes
            shallow <- firstCheck 0
            deep <- firstCheck 16
            assertBool "scoping forced collection lowering throughout the unused catalog" (deep <= 2 * shallow + 131072)
        , localScopeTests
        , pruningTests
        , testCaseInfo "changing local scopes reuse base sort coordinates" $ do
            (shared, rebuilt) <- localCheckingAllocation
            let report = "shared/rebuilt local scopes allocated " ++ show (shared, rebuilt)
            assertBool report (shared * 4 <= rebuilt * 3 + 131072)
            pure report
        , testCase "constraint locations share the immutable declaration preparation" $ do
            let declarations =
                    F.emptySymEnv
                        { F.seSort = F.fromListSEnv [(F.symbol ("constraint_catalog_" ++ show index), F.FFunc F.FInt (F.setSort F.FInt)) | index <- [1 :: Int .. 4096]]
                        }
                parameter = C.ElabParam (Config.ElabFlags True False) "constraint catalog control" declarations
                candidates =
                    [ F.SimpC F.emptyIBindEnv (F.PAtom F.Eq literal literal) (Just index) 0 [] location
                    | index <- [1 .. 64]
                    , let literal = F.ECon (F.I index)
                          position = F.safeSourcePos "constraint-catalog.hs" (fromInteger index) 1
                          location = F.SS position position
                    ]
                outputs = map (C.elaborate parameter) candidates
                expected = map (C.elaborate parameter{C.epEnv = F.emptySymEnv} . F._crhs) candidates
            _ <- evaluate (force (declarations, candidates, expected))
            bytes <- allocationBytes outputs
            map F._crhs outputs @?= expected
            map F._cid outputs @?= map F._cid candidates
            map F._cinfo outputs @?= map F._cinfo candidates
            assertBool ("each constraint rebuilt the declaration preparation: " ++ show bytes ++ " bytes") (bytes <= 8 * 1024 * 1024)
        , testGroup
            "refinement elaboration shares immutable declarations"
            [ testCase label $ do
                let declarations =
                        F.emptySymEnv
                            { F.seSort =
                                F.fromListSEnv
                                    [ ( F.symbol ("refinement_catalog_" ++ show index)
                                      , if nested then F.FObj (F.symbol ("nominal_" ++ show index)) else F.FFunc F.FInt (F.setSort F.FInt)
                                      )
                                    | index <- [1 :: Int .. 4096]
                                    ]
                            }
                    parameter = C.ElabParam (Config.ElabFlags True False) "refinement catalog control" declarations
                    candidates =
                        [ F.RR F.FInt (F.Reft (value, F.PAtom F.Eq actual (F.ECon (F.I (fromIntegral index)))))
                        | index <- [1 :: Int .. 64]
                        , let value = F.symbol ("value_" ++ show index)
                              actual =
                                if nested
                                    then F.EApp (F.ELam ("inner", F.FInt) (F.EBin F.Plus (F.EVar "inner") (F.EVar value))) (F.ECon (F.I 0))
                                    else F.EVar value
                        ]
                    entries =
                        [ (index, (F.symbol ("binding_" ++ show index), candidate, F.SS position position))
                        | (index, candidate) <- zip [1 ..] candidates
                        , let position = F.safeSourcePos "refinement-catalog.hs" index 1
                        ]
                    expected = C.elaborate parameter{C.epEnv = F.emptySymEnv} candidates
                    outputs =
                        if withLocations
                            then [refinement | (_, (_, refinement, _)) <- sortOn fst (F.bindEnvToList (C.elaborate parameter (F.bindEnvFromList entries)))]
                            else C.elaborate parameter candidates
                _ <- evaluate (force (declarations, entries, expected))
                bytes <- allocationBytes outputs
                outputs @?= expected
                assertBool ("refinement rows rebuilt the catalog: " ++ show bytes) (bytes <= 8 * 1024 * 1024)
            | (label, withLocations, nested) <-
                [ ("direct list", False, False)
                , ("distinct binding locations", True, False)
                , ("nested predicates and nominal catalog", False, True)
                , ("nested predicates at distinct binding locations", True, True)
                ]
            ]
        , testGroup
            "sort inference shares declaration coordinates"
            [ testCase label $ do
                let declarations = F.fromListSEnv [(F.symbol ("inference_catalog_" ++ show index), F.FVar index) | index <- [1 .. 4096]]
                    candidates :: [F.Expr]
                    candidates = [F.PAtom F.Eq literal literal | index <- [1 .. 64], let literal = F.ECon (F.I index)]
                    outputs = map (infer declarations) candidates
                    expected = map (infer mempty) candidates
                _ <- evaluate (force (declarations, candidates, expected))
                bytes <- allocationBytes outputs
                expected @?= replicate 64 (Just F.boolSort)
                outputs @?= expected
                assertBool ("each expression rebuilt the declaration inventory: " ++ show bytes ++ " bytes") (bytes <= 8 * 1024 * 1024)
            | (label, infer) <- [("sortExpr", \environment -> Just . C.sortExpr Nothing F.dummySpan environment), ("checkSortExpr", C.checkSortExpr Nothing F.dummySpan)]
            ]
        , testCase "discarding a sort error does not render spelling alternatives" $ do
            let declarations = F.fromListSEnv [(F.symbol (replicate 256 'a' ++ show index), F.FInt) | index <- [1 :: Int .. 64]]
                input :: F.Expr
                input = F.EVar (F.symbol (replicate 256 'b'))
                output = C.checkSortExpr Nothing F.dummySpan declarations input
            _ <- evaluate (force (declarations, input))
            bytes <- allocationBytes output
            output @?= Nothing
            assertBool ("discarded diagnostic rendered alternatives: " ++ show bytes ++ " bytes") (bytes <= 128 * 1024)
        ]
  where
    flags = Config.ElabFlags False False

pruningTests :: TestTree
pruningTests =
    testGroup
        "pruning shares independent sort judgments"
        ( [ testCase label $
                C.pruneUnsortedReft (F.fromListSEnv declarations) templates (F.RR source (F.Reft (name, input)))
                    @?= F.RR expectedSort (F.Reft (name, expected))
          | (label, declarations, templates, source, name, input, expectedSort, expected) <-
                [ ("Bool enforcement and lexical value shadowing", [("value", F.boolSort)], F.anything, F.FInt, "value", F.PAnd [zero, valid, invalid], F.FInt, valid)
                , ("fractional declaration survives an integral lexical namesake", [("alpha", F.FFrac), ("x", F.FObj "alpha")], F.anything, F.FInt, "alpha", modulo, F.FInt, F.PTrue)
                , ("integral declaration permits modulo", [("alpha", F.FNum), ("x", F.FObj "alpha")], F.anything, F.FInt, "alpha", modulo, F.FInt, modulo)
                , ("source sort closes against numeric declarations", [("alpha", F.FFrac)], F.anything, F.FObj "alpha", "value", fractional, F.FReal, fractional)
                , ("lexical values do not supply nominal aliases", [], F.anything, F.boolSort, "alpha", equal (F.ECon (F.L "nominal" (F.FObj "alpha"))) F.PTrue, F.boolSort, F.PTrue)
                , ("selective templates leave unmatched expressions alone", [], selected, F.FInt, "value", F.PAnd [zero, invalid, equalValue], F.FInt, F.pAnd [zero, equalValue])
                , ("empty templates preserve the original refinement", [("alpha", F.FFrac)], mempty, F.FObj "alpha", "value", F.PAnd [zero, invalid], F.FObj "alpha", F.PAnd [zero, invalid])
                , ("each conjunct gets fresh equations after success and failure", [("f", F.FVar 9)], F.anything, F.FInt, "value", F.PAnd [integerCall, F.PImp integerCall booleanCall, booleanCall], F.FInt, F.pAnd [integerCall, booleanCall])
                ]
          ]
            ++ [ testCaseInfo "conjuncts reuse the declaration inventory" $ do
                    narrowFirst <- pruningAllocation 256 2
                    narrowMany <- pruningAllocation 256 32
                    wideFirst <- pruningAllocation 4096 2
                    wideMany <- pruningAllocation 4096 32
                    assertBool
                        ("pruning widths/conjuncts allocated " ++ show (narrowFirst, narrowMany, wideFirst, wideMany))
                        (wideMany <= 4 * wideFirst + 4 * narrowMany + 2 * 1024 * 1024)
                    pure ("pruning widths/conjuncts allocated " ++ show (narrowFirst, narrowMany, wideFirst, wideMany))
               ]
        )
  where
    zero = F.ECon (F.I 0)
    value = F.EVar "value"
    equal = F.PAtom F.Eq
    valid = F.PAtom F.Ge value zero
    invalid = equal value F.PTrue
    equalValue = equal value zero
    fractional = F.PAtom F.Ge value (F.ECon (F.R 0.5))
    modulo = equal (F.EBin F.Mod (F.EVar "x") (F.ECon (F.I 2))) zero
    integerCall = equal (F.EApp (F.EVar "f") zero) zero
    booleanCall = equal (F.EApp (F.EVar "f") F.PTrue) F.PTrue
    selected = F.makeTemplates [(["left", "right"], equal (F.EVar "left") (F.EVar "right"))]

pruningAllocation :: Int -> Int -> IO Integer
pruningAllocation width count = do
    let declarations =
            F.fromListSEnv
                (("value", F.boolSort) : [(F.symbol ("pruning_" ++ show index), F.FAbs index (F.FFunc (F.FVar index) F.FInt)) | index <- [1 .. width]])
        comparison index = F.PAtom F.Ge (F.EVar "value") (literal index)
        literal index = F.ECon (F.I (fromIntegral index))
        predicate index
            | index `mod` 7 == 0 = F.PAtom F.Eq (F.EVar "value") (F.ECst (literal index) F.boolSort)
            | otherwise = comparison index
        input = F.RR F.FInt (F.Reft ("value", F.PAnd (map predicate [1 .. count])))
        output = C.pruneUnsortedReft declarations F.anything input
        expected = F.RR F.FInt (F.Reft ("value", F.pAnd [comparison index | index <- [1 .. count], index `mod` 7 /= 0]))
    _ <- evaluate (force (declarations, input))
    bytes <- allocationBytes output
    output @?= expected
    pure bytes

localScopeTests :: TestTree
localScopeTests =
    testGroup
        "prepared local declaration scopes"
        [ testCase "unused and overwritten declarations preserve nominal judgments" $
            checkCases
                [("unused", F.FObj "alpha")]
                [([], nominalEquality), ([("unused", F.FInt)], nominalEquality), ([], nominalEquality)]
                [True, True, True]
        , testCase "unused sort support preserves term binding and implicit actuals" $
            mapM_
                ( \body -> do
                    let base = F.fromListSEnv [("unused", F.FObj "alpha")]
                        local = F.fromListSEnv [("unused", F.FInt)]
                        input = F.ELam ("alpha", F.boolSort) body
                        elaborateAt declarations = Vis.stripCasts . C.elabExpr (C.ElabParam flags "unused support" (F.emptySymEnv{F.seSort = declarations})) Nothing
                        shared = elaborateAt base input
                        rebuilt = elaborateAt (local <> base) input
                    shared @?= rebuilt
                    map (C.checkSortExpr Nothing F.dummySpan (local <> base)) [shared, rebuilt] @?= replicate 2 (Just (F.FFunc F.boolSort F.boolSort))
                    case (shared, rebuilt) of
                        (F.ELam (sharedName, _) sharedBody, F.ELam (rebuiltName, _) rebuiltBody) -> do
                            (sharedName, rebuiltName) @?= ("alpha", "alpha")
                            case (sharedBody, rebuiltBody) of
                                (F.EVar sharedOccurrence, F.EVar rebuiltOccurrence) -> (sharedOccurrence, rebuiltOccurrence) @?= (sharedName, rebuiltName)
                                (F.PKVar _ _ sharedActuals, F.PKVar _ _ rebuiltActuals) -> do
                                    F.fromKVarSubst sharedActuals @?= M.empty
                                    F.fromKVarSubst rebuiltActuals @?= M.empty
                                _ -> assertBool "binder body changed shape" False
                        _ -> assertBool "term binder changed shape" False
                )
                [F.EVar "alpha", F.PKVar (F.KV "implicit") mempty mempty]
        , testGroup
            "term alpha-renaming preserves declaration-owned annotations"
            [ testCase (label ++ " / " ++ show weakened) $ do
                let declarations = if weakened then F.fromListSEnv [("unused", F.FObj "alpha")] else mempty
                    renamed = F.substr (S.fromList ["alpha"]) (F.mkSubst []) input
                    parameter = C.ElabParam flags "term sort ownership" (F.emptySymEnv{F.seSort = declarations})
                C.checkSortExpr Nothing F.dummySpan declarations input @?= Just expected
                C.checkSortExpr Nothing F.dummySpan declarations renamed @?= Just expected
                output <- evaluate (force (C.elabExpr parameter Nothing input))
                C.checkSortExpr Nothing F.dummySpan declarations output @?= Just expected
            | let nominalSort = F.FObj "alpha"
                  literal = F.ECon (F.L "nominal" nominalSort)
                  list = F.fAppTC F.listFTyCon [nominalSort]
            , (label, input, expected) <-
                [ ("lambda owns terms, not its domain", F.ELam ("alpha", list) (F.EVar "alpha"), F.FFunc list list)
                , ("lambda result remains nominal", F.EApp (F.ELam ("alpha", F.boolSort) literal) F.PTrue, nominalSort)
                , ("inferred let does not bind a nominal coordinate", F.ELet "alpha" (F.EIte F.PTrue F.PTrue F.PFalse) (F.EIte (F.EVar "alpha") literal literal), nominalSort)
                ]
            , weakened <- [False, True]
            ]
        , testCase "term shadowing preserves an ambient equality alias and its inference coordinate" $ do
            let predicate = F.PAll [("alpha", F.boolSort)] (equal (F.ECon (F.L "nominal" (F.FObj "alpha"))) F.PTrue)
            C.checkSortExpr Nothing F.dummySpan (F.fromListSEnv [("alpha", F.FVar 0)]) predicate @?= Just F.boolSort
            C.checkSortExpr Nothing F.dummySpan mempty predicate @?= Nothing
            C.checkSortExpr Nothing F.dummySpan mempty (F.ELam ("alpha", F.boolSort) (F.ECst (F.ECon (F.L "nominal" (F.FObj "alpha"))) F.boolSort)) @?= Nothing
        , testCase "type abstraction owns sort coordinates independently of term binders" $ do
            let declarations = F.fromListSEnv [("alpha", F.FFrac)]
                input = F.ETAbs (F.ELam ("alpha", F.boolSort) (F.ECst (F.EVar "alpha") (F.FObj "alpha"))) "alpha"
                output = elaborateOpaque declarations input
            case output of
                Just (F.ETAbs (F.ELam (term, _) (F.ECst (F.EVar occurrence) (F.FObj coordinate))) owner) -> do
                    assertBool "type binder captured ambient alias" (owner /= "alpha")
                    term @?= "alpha"
                    occurrence @?= term
                    coordinate @?= owner
                _ -> assertBool "type abstraction lost its owned coordinate" False
        , testCase "opaque type scopes retain their bound coordinate and close ambient annotations" $ do
            let base = F.fromListSEnv [("hidden", F.FObj "alpha"), ("number", F.FFrac)]
                local = F.fromListSEnv [("hidden", F.FInt), ("number", F.FNum)]
                input = F.ETAbs (F.ECoerc (F.FObj "alpha") (F.FObj "number") (F.ECon (F.L "bound" (F.FObj "alpha")))) "alpha"
                shared = elaborateOpaque base input
                rebuilt = elaborateOpaque (local <> base) input
            case (shared, rebuilt) of
                (Just (F.ETAbs sharedBody sharedOwner), Just (F.ETAbs rebuiltBody rebuiltOwner)) -> do
                    sharedBody @?= F.ECoerc (F.FObj sharedOwner) F.FReal (F.ECon (F.L "bound" (F.FObj sharedOwner)))
                    rebuiltBody @?= F.ECoerc (F.FObj rebuiltOwner) F.FInt (F.ECon (F.L "bound" (F.FObj rebuiltOwner)))
                _ -> assertBool "type abstraction lost its owned coordinate" False
        , testCase "an opaque type binder cannot capture a free solved sort image" $ do
            let declarations = F.fromListSEnv [("x", F.FVar 9), ("y", F.FObj "alpha")]
                actual = F.ETAbs (F.ECoerc (F.FObj "alpha") (F.FVar 9) F.PTrue) "alpha"
                input = F.PAnd [equal (F.EVar "x") (F.EVar "y"), opaque actual]
                parameter = C.ElabParam flags "opaque substitution image" (F.emptySymEnv{F.seSort = declarations})
            case C.elabExpr parameter Nothing input of
                F.PAnd [_, F.PKVar _ _ actuals] -> case M.lookup "argument" (F.fromKVarSubst actuals) of
                    Just (F.ETAbs (F.ECoerc (F.FObj bound) (F.FObj free) F.PTrue) owner) -> do
                        bound @?= owner
                        free @?= "alpha"
                        assertBool "free substitution image became type-bound" (owner /= free)
                    _ -> assertBool "opaque actual changed shape" False
                _ -> assertBool "opaque occurrence changed shape" False
        , testCase "local kinds override base kinds without pre-closing inherited aliases" $
            checkCases
                [("alpha", F.FFrac), ("x", F.FObj "alpha")]
                [([], modulo), ([("alpha", F.FNum)], modulo), ([], modulo)]
                [False, True, False]
        , testCase "fractional local kinds do not leak to sibling numeric scopes" $
            checkCases
                [("alpha", F.FNum), ("x", F.FObj "alpha")]
                [([], modulo), ([("alpha", F.FFrac)], modulo), ([], modulo)]
                [True, False, True]
        , testCase "changing declarations keep independent substitutions and deferred obligations" $
            checkCases
                [("x", F.FVar 9)]
                [ ([("local", F.FInt)], F.PAnd [F.PAtom F.Ueq (F.EVar "x") zero, equal (F.EVar "x") F.PTrue])
                , ([("local", F.boolSort)], equal (F.EVar "x") F.PTrue)
                , ([("local", F.FReal)], equal (F.EVar "x") zero)
                ]
                [False, True, True]
        , testCase "overwritten base indices and live local indices remain capture-safe" $
            checkCases
                [("f", scheme), ("unused", F.FVar 0)]
                [ ([("unused", F.boolSort), ("local", F.FVar 1)], F.PAnd [freshBoolean, equal (F.EVar "local") zero])
                , ([("unused", F.FInt), ("local", F.FVar 0)], F.PAnd [freshBoolean, equal (F.EVar "local") zero])
                ]
                [True, True]
        , testCase "expected coordinates remain reserved alongside local declarations" $ do
            let checkAt = runReader (C.prepareSortCheck Nothing (F.fromListSEnv [("f", scheme), ("unused", F.FAbs 42 (F.FVar 2))])) flags
                local = F.fromListSEnv [("local", F.FVar 1)]
                body = F.ELam ("x", F.FVar 9) (F.PAnd [freshBoolean, equal (F.EVar "x") zero])
            fmap show (C.checkSortAt (C.extendSortCheck local checkAt) F.dummySpan (Just (F.FFunc (F.FVar 0) F.boolSort)) body) @?= Nothing
        , testCase "partial local preparation does not demand an unused local environment" $ do
            let checkAt = runReader (C.prepareSortCheck Nothing mempty) flags
            _ <- evaluate (C.extendSortCheck (error "unused local environment forced") checkAt)
            pure ()
        , testGroup
            "pointwise normalization preserves local shadowing"
            [ testCase (show lowerSets) $ do
                let source = F.mapSort F.FInt (F.setSort F.FInt)
                    other = F.mapSort F.FInt (F.setSort F.FReal)
                    base = F.fromListSEnv [("x", source)]
                    checkAt = runReader (C.prepareSortCheck Nothing base) (Config.ElabFlags lowerSets False)
                    candidate = F.RR source (F.Reft ("value", equal (F.EVar "x") (F.ECst (F.EVar "x") source)))
                    locals = [mempty, F.fromListSEnv [("x", other)], mempty]
                    results = [fmap show (C.checkSortAt (C.extendSortCheck local checkAt) F.dummySpan Nothing candidate) | local <- locals]
                map isNothing results @?= [True, False, True]
                results @?= [fmap show (runReader (C.checkSorted Nothing F.dummySpan (local <> base) candidate) (Config.ElabFlags lowerSets False)) | local <- locals]
            | lowerSets <- [False, True]
            ]
        ]
  where
    flags = Config.ElabFlags True False
    opaque actual = F.PKVar (F.KV "opaque") mempty (F.toKVarSubst (M.singleton "argument" actual))
    elaborateOpaque declarations actual =
        case C.elabExpr (C.ElabParam flags "opaque type scope" (F.emptySymEnv{F.seSort = declarations})) Nothing (opaque actual) of
            F.PKVar _ _ actuals -> M.lookup "argument" (F.fromKVarSubst actuals)
            _ -> Nothing
    checkCases :: [(F.Symbol, F.Sort)] -> [([(F.Symbol, F.Sort)], F.Expr)] -> [Bool] -> IO ()
    checkCases declarations candidates expected = do
        let base = F.fromListSEnv declarations
            checkAt = runReader (C.prepareSortCheck Nothing base) flags
            results = [fmap show (C.checkSortAt (C.extendSortCheck (F.fromListSEnv local) checkAt) F.dummySpan Nothing predicate) | (local, predicate) <- candidates]
            rebuilt = [fmap show (runReader (C.checkSorted Nothing F.dummySpan (F.fromListSEnv local <> base) predicate) flags) | (local, predicate) <- candidates]
        results @?= rebuilt
        map isNothing results @?= expected
    zero, freshBoolean, modulo, nominal, nominalEquality :: F.Expr
    zero = F.ECon (F.I 0)
    equal :: F.Expr -> F.Expr -> F.Expr
    equal = F.PAtom F.Eq
    scheme = F.FAbs 42 (F.FFunc F.FInt (F.FVar 42))
    freshBoolean = equal (F.EApp (F.EVar "f") zero) F.PTrue
    modulo = equal (F.EBin F.Mod (F.EVar "x") (F.ECon (F.I 2))) zero
    nominal = F.EApp (F.ELam ("alpha", F.boolSort) (F.ECon (F.L "nominal" (F.FObj "alpha")))) F.PTrue
    nominalEquality = equal nominal nominal

groundInventoryTests :: TestTree
groundInventoryTests =
    testGroup
        "ground judgments do not demand unused coordinates"
        [ testCaseInfo label $ do
            let measure width = do
                    let declarations =
                            F.fromListSEnv
                                [ (F.symbol ("unused_coordinate_" ++ show index), F.FAbs (2 * index) (F.FFunc (F.FVar (2 * index)) (F.FVar (2 * index + 1))))
                                | index <- [1 .. width]
                                ]
                        output = action declarations
                    _ <- evaluate (force (declarations, literal, expected))
                    bytes <- allocationBytes output
                    output @?= expected
                    pure bytes
            narrow <- measure 16
            wide <- measure 4096
            let report = "unused catalog widths allocated " ++ show (narrow, wide)
            assertBool report (wide <= 4 * narrow + 131072)
            pure report
        | (label, action, expected) <-
            [ ("sortExprE", \environment -> show (C.sortExprE Nothing F.dummySpan environment mempty literal), show (Right F.FInt :: Either F.Error F.Sort))
            , ("elabExprE", \environment -> show (C.elabExprE (C.ElabParam flags "unused coordinates" F.emptySymEnv{F.seSort = environment}) Nothing literal), show (Right literal :: Either F.Error F.Expr))
            , ("prepareSortCheck", \environment -> show (fmap show (C.checkSortAt (runReader (C.prepareSortCheck Nothing environment) flags) F.dummySpan (Just F.FInt) literal)), show (Nothing :: Maybe String))
            , ("unifyTo1", \environment -> show (C.unifyTo1 (C.mkSearchEnv environment) [F.FInt, F.FInt]), show (Just F.FInt))
            ]
                ++ [ ( "unifyFastWith " ++ show exact
                     , \environment -> show (fmap (\solution -> C.apply solution (F.FVar 9)) (C.unifyFastWith (C.sortFieldIndices environment) exact (C.mkSearchEnv environment) F.FInt F.FInt))
                     , show (Just (F.FVar 9))
                     )
                   | exact <- [False, True]
                   ]
        ]
  where
    literal :: F.Expr
    literal = F.ECon (F.I 1)
    flags = Config.ElabFlags False False

substitutionAllocation :: (NFData s) => (Int -> s) -> (s -> F.Sort -> F.Sort) -> F.Sort -> F.Sort -> IO ()
substitutionAllocation makeSubstitution action selected absent = do
    let measure width = do
            let substitution = makeSubstitution width
                inputs = [F.FFunc coordinate (F.FNatNum index) | index <- [1 .. 128], coordinate <- [selected, absent]]
                expected = [F.FFunc coordinate (F.FNatNum index) | index <- [1 .. 128], coordinate <- [F.FInt, absent]]
                outputs = map (action substitution) inputs
            _ <- evaluate (force (substitution, inputs))
            bytes <- allocationBytes outputs
            outputs @?= expected
            pure bytes
    narrow <- measure 16
    wide <- measure 4096
    assertBool ("substitution scanned unrelated images: " ++ show (narrow, wide)) (wide <= 4 * narrow + 131072)

localCheckingAllocation :: IO (Integer, Integer)
localCheckingAllocation = do
    let signature = foldl' (\body index -> F.FFunc (F.setSort (F.FVar index)) body) F.FInt [0 .. 31]
        base = F.fromListSEnv (("poly", F.FAbs 42 (F.FFunc (F.FVar 42) (F.FVar 42))) : [(F.symbol ("unused" ++ show index), signature) | index <- [1 :: Int .. 128]])
        cases :: [(F.SEnv F.Sort, F.Expr)]
        cases =
            [ (F.fromListSEnv [("local", F.FInt), ("scope", F.FObj (F.symbol ("scope" ++ show index)))], F.PAtom F.Eq (F.EApp (F.EVar "poly") (F.EVar "local")) (F.ECon (F.I index)))
            | index <- [1 .. 64]
            ]
        flags = Config.ElabFlags True False
        checkAt = runReader (C.prepareSortCheck Nothing base) flags
        shared = [fmap show (C.checkSortAt (C.extendSortCheck local checkAt) F.dummySpan Nothing predicate) | (local, predicate) <- cases]
        rebuilt = [fmap show (runReader (C.checkSorted Nothing F.dummySpan (local <> base) predicate) flags) | (local, predicate) <- cases]
    _ <- evaluate (force (base, cases))
    sharedBytes <- allocationBytes shared
    rebuiltBytes <- allocationBytes rebuilt
    shared @?= replicate (length cases) Nothing
    rebuilt @?= shared
    pure (sharedBytes, rebuiltBytes)

checkingAllocation :: Int -> Maybe F.Sort -> IO Integer
checkingAllocation width expected = do
    let environment = F.fromListSEnv (("x", F.FInt) : [(name "unused" index, F.FObj (name "sort" index)) | index <- [1 .. width]])
        candidates =
            [ F.RR F.FInt (F.Reft (name "value" index, F.PAll [("bound", F.FInt)] (F.PAtom F.Eq (F.EVar "x") (if index `mod` 7 == 0 then F.PTrue else F.ECon (F.I (fromIntegral index))))))
            | index <- [1 .. 128]
            ]
        checkAt = C.checkSortAt (runReader (C.prepareSortCheck Nothing environment) (Config.ElabFlags True False))
        results = map (isNothing . checkAt F.dummySpan expected) candidates
    _ <- evaluate (force (environment, candidates))
    bytes <- allocationBytes results
    results @?= [index `mod` 7 /= 0 | index <- [1 :: Int .. 128]]
    pure bytes
  where
    name :: String -> Int -> F.Symbol
    name prefix index = F.symbol (prefix ++ show index)

reference :: (G.Data a) => a -> S.HashSet Int
reference = G.everything S.union (G.mkQ S.empty F.sortIndices)

nested :: F.Sort
nested = F.FAbs (-7) (F.FFunc (F.FVar 12) (F.FAbs maxBound (F.FAbs 19 (F.FVar 12))))

kvar, expression :: F.Expr
kvar =
    F.PKVar
        (F.KV "k")
        (M.singleton "type" (F.FAbs 31 (F.FVar 32)))
        (F.mkKVarSubst [("actual", F.ECst (F.EVar "x") (F.FFunc (F.FVar 33) (F.FVar 34)))])
expression =
    F.PAll [("bound", nested)] $
        F.PAnd
            [ kvar
            , F.PAtom
                F.Eq
                (F.ECoerc (F.FVar 41) (F.FVar 42) (F.ETApp (F.EVar "poly") (F.FVar 43)))
                (F.ECon (F.L "literal" (F.FVar 44)))
            ]

catalog :: F.SymEnv
catalog =
    F.emptySymEnv
        { F.seSort = F.fromListSEnv [("term", F.FVar 51)]
        , F.seTheory = F.fromListSEnv [("native", F.Thy "native" "raw name" (F.FAbs 52 (F.FVar 53)) F.Theory)]
        }

largeCatalog :: F.SymEnv
largeCatalog =
    F.emptySymEnv
        { F.seSort = F.fromListSEnv [(name index, scheme index) | index <- [0 .. 255]]
        , F.seTheory = F.fromListSEnv [(name index, F.Thy (name index) "native" (scheme index) F.Theory) | index <- [256 .. 511]]
        }
  where
    name :: Int -> F.Symbol
    name index = F.symbol ("catalog_" ++ show index)
    scheme :: Int -> F.Sort
    scheme index = F.FAbs (1000 + index) (F.FFunc (F.FVar index) (F.FVar (1000 + index)))

envelope :: Envelope
envelope = Envelope "owner" "metadata" "file path" 999 [nested, F.FVar 61] expression

allocation :: Int -> IO Integer
allocation width = do
    let rows :: [(F.Symbol, T.Text, String, F.Sort)]
        rows =
            [ (F.symbol spelling, T.pack spelling, spelling, F.FVar index)
            | index <- [70 .. 77]
            , let spelling = show index ++ replicate width 'a'
            ]
        forceNames =
            sum
                [ T.length (F.symbolText symbol)
                    + T.length (F.symbolSafeText symbol)
                    + T.length text
                    + length spelling
                | (symbol, text, spelling, _) <- rows
                ]
    _ <- evaluate forceNames
    _ <- evaluate (force (map (\(_, _, _, sort) -> sort) rows))
    let result = C.sortFieldIndices rows
    bytes <- allocationBytes result
    result @?= S.fromList [70 .. 77]
    pure bytes

-- Thread-local counters keep allocation bounds independent of parallel tests.
-- Callers fully evaluate input fixtures before measuring the demanded result.
allocationBytes :: (NFData a) => a -> IO Integer
allocationBytes result = do
    before <- getAllocationCounter
    _ <- evaluate (force result)
    after <- getAllocationCounter
    pure (toInteger before - toInteger after)
