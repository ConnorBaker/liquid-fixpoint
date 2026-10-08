{-# LANGUAGE OverloadedStrings #-}

module PreparedElaborationTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate, try)
import Control.Monad.IO.Class (liftIO)
import Data.Either (isRight)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (isInfixOf, isPrefixOf, mapAccumL)
import qualified Data.Text as T
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.Solver.UniqifyBinds as Rename
import qualified Language.Fixpoint.Solver.UniqifyKVars as KVars
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import qualified Language.Fixpoint.Types.Solutions as Sol
import NativeCallableTests (withSMT)
import SourceCheckScopeTests (jointSorts)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests =
    testGroup "prepared elaboration scope" $
        [ testGroup
            label
            [ testCase "independent results keep their Bool sort in either order" $ do
                let elaborateAt = prepare (parameter [("f", F.FVar 9)])
                mapM (observe elaborateAt) [integerCall, booleanCall, booleanCall, integerCall]
                    >>= (@?= replicate 4 (Right (Just F.boolSort)))
            , testCase "one expression still owns coherent equations" $ do
                let elaborateAt = prepare (parameter [("f", F.FVar 9)])
                observe elaborateAt (F.PAnd [integerCall, booleanCall]) >>= assertSortError "Cannot unify"
                observe elaborateAt integerCall >>= (@?= Right (Just F.boolSort))
            , testCase "a fresh function shape cannot contain its own argument sort" $ do
                let elaborateAt = prepare (parameter [("f", F.FVar 9)])
                observe elaborateAt (F.EApp (F.EVar "f") (F.EVar "f")) >>= assertSortError "infinite free sort"
                observe elaborateAt integerCall >>= (@?= Right (Just F.boolSort))
            , testCase "separate forall occurrences remain independent within one expression" $ do
                let elaborateAt = prepare (parameter [("f", F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 0)))])
                observe elaborateAt (F.PAnd [integerCall, booleanCall]) >>= (@?= Right (Just F.boolSort))
            ]
        | (label, prepare) <- [("elaborate", C.elaborate), ("elabExpr", \ep -> C.elabExpr ep Nothing)]
        ]
            ++ [fresheningTests, closureWhnfTests, constraintTests, refinementTests, inferenceTests, querySortTests, relationalSetTests, stringRoundTripTests, solutionScopeTests, binderRepresentationTests]
            ++ [ testCase ("WF telescope preserves every origin: " ++ show (length values)) $ do
                    let kvar = F.KV "value-telescope"
                        scope = F.fromListIBindEnv [0]
                        occurrence = F.PKVar kvar mempty (F.mkKVarSubst [(name, F.EVar name) | (name, _) <- values ++ [("ordinary", F.FInt)]])
                        reft predicate = F.RR F.boolSort (F.Reft ("v", predicate))
                        input =
                            (mempty :: F.FInfo ())
                                { F.bs = F.bindEnvFromList [(0, ("ordinary", F.trueSortedReft F.FInt, ()))]
                                , F.ws = M.singleton kvar (F.WfC scope values kvar ())
                                , F.cm = M.singleton 1 (F.mkSubC scope (reft F.PTrue) (reft occurrence) (Just 1) [] ())
                                }
                    (_, _, processed, sources) <- Solver.simplifyFInfo Config.defConfig{Config.noEnvReduction = True} input
                    let normalized = F.wvvs (F.ws processed M.! kvar)
                        recorded = sources M.! kvar
                        valueRows = [(name, F.sr_sort sr) | (_, (name, sr, _)) <- F.bindEnvToList (F.bs processed), name `elem` map fst normalized]
                    map snd normalized @?= map snd values
                    S.fromList valueRows @?= S.fromList normalized
                    S.fromList (M.elems recorded) @?= S.fromList ("ordinary" : map fst values)
                    S.fromList (F.kvarDomain processed kvar) @?= M.keysSet recorded
               | values <- [[], [("first", F.FInt), ("second", F.boolSort), ("third", F.FReal)]]
               ]
            ++ [ testCase "WF alpha-renaming preserves KVar actuals" $ do
                    let kvar = F.KV "collision"
                        generated = F.kArgSymbol "x" (F.kv kvar)
                        scope = F.fromListIBindEnv [0]
                        reft predicate = F.RR F.boolSort (F.Reft ("v", predicate))
                        occurrence = F.PKVar kvar mempty (F.mkKVarSubst [("x", F.EVar "x")])
                        input =
                            (mempty :: F.FInfo ())
                                { F.bs = F.bindEnvFromList [(0, ("x", F.trueSortedReft F.FInt, ())), (1, (generated, F.trueSortedReft F.FReal, ()))]
                                , F.ws = M.singleton kvar (F.WfC scope [("v", F.boolSort)] (kvar) ())
                                , F.cm = M.singleton 1 (F.mkSubC scope (reft F.PTrue) (reft occurrence) (Just 1) [] ())
                                }
                    (_, _, processed, sources) <- Solver.simplifyFInfo Config.defConfig{Config.noEnvReduction = True} input
                    let canonical = F.kvarDomain processed kvar
                        actuals = [F.fromKVarSubst su | constraint <- M.elems (F.cm processed), su <- M.lookupDefault [] kvar (F.exprKVars (F.crhs constraint))]
                    assertBool ("canonical=" ++ show canonical ++ " actuals=" ++ show actuals) (length canonical == 2 && all (\key -> any (M.member key) actuals) canonical)
                    fmap (S.fromList . M.elems) (M.lookup kvar sources) @?= Just (S.fromList ["x", "v"])
               , testCase "WF canonicalization preserves colliding source actuals" $ do
                    let kvar = F.KV "source-collision"
                        generated = F.kArgSymbol "x" (F.kv kvar)
                        scope = F.fromListIBindEnv [0, 1]
                        occurrence = F.PKVar kvar mempty (F.mkKVarSubst [("x", F.EVar "x"), (generated, F.EVar generated)])
                        input =
                            (mempty :: F.SInfo ())
                                { F.bs = F.bindEnvFromList [(0, ("x", F.trueSortedReft F.FInt, ())), (1, (generated, F.trueSortedReft F.FReal, ()))]
                                , F.ws = M.singleton kvar (F.WfC scope [("v", F.boolSort)] (kvar) ())
                                , F.cm = M.singleton 1 (F.SimpC scope occurrence (Just 1) 0 [] ())
                                }
                        (_, processed) = KVars.wfcUniqify input
                    let actuals = [F.fromKVarSubst su | constraint <- M.elems (F.cm processed), su <- M.lookupDefault [] kvar (F.exprKVars (F.crhs constraint))]
                        values = concatMap M.elems actuals
                    assertBool ("source actual disappeared: " ++ show actuals) (F.EVar "x" `elem` values && F.EVar generated `elem` values)
               , testCase "alpha-renaming reserves existing source names" $ do
                    let occupied0 = F.renameSymbol "x" 0
                        occupied1 = F.renameSymbol "x" 1
                        bindings = [(0, ("x", F.trueSortedReft F.FInt, ())), (1, ("x", F.trueSortedReft F.FReal, ())), (2, (occupied0, F.trueSortedReft F.boolSort, ())), (3, (occupied1, F.trueSortedReft (F.FObj "Other"), ()))]
                        output = Rename.renameAll (mempty{F.bs = F.bindEnvFromList bindings} :: F.SInfo ())
                        names = [sym | (_, (sym, _, _)) <- F.bindEnvToList (F.bs output)]
                    assertBool ("renamed bindings collide: " ++ show names) (length names == 4 && S.size (S.fromList names) == 4)
               , testCase "alpha-renaming reserves declared globals" $ do
                    let occupied = [F.renameSymbol "x" 0, F.renameSymbol "x" 1]
                        bindings = [(0, ("x", F.trueSortedReft F.FInt, ())), (1, ("x", F.trueSortedReft F.FReal, ()))]
                        input = (mempty :: F.SInfo ()){F.bs = F.bindEnvFromList bindings, F.gLits = F.fromListSEnv [(name, F.boolSort) | name <- occupied]}
                        output = Rename.renameAll input
                        names = [sym | (_, (sym, _, _)) <- F.bindEnvToList (F.bs output)]
                    assertBool ("renamed binder captured a global: " ++ show names) (all (`notElem` names) occupied)
               , testCase "alpha-renaming reserves reflected definitions" $ do
                    let occupied = [F.renameSymbol "x" 0, F.renameSymbol "x" 1]
                        bindings = [(0, ("x", F.trueSortedReft F.FInt, ())), (1, ("x", F.trueSortedReft F.FReal, ()))]
                        definitions = [F.Equ name [] F.PTrue F.boolSort False | name <- occupied]
                        input = (mempty :: F.SInfo ()){F.bs = F.bindEnvFromList bindings, F.ae = mempty{F.aenvEqs = definitions}}
                        output = Rename.renameAll input
                        names = [sym | (_, (sym, _, _)) <- F.bindEnvToList (F.bs output)]
                    assertBool ("renamed binder captured a reflected definition: " ++ show names) (all (`notElem` names) occupied)
               ]
            ++ [ testCase "Either elaboration resets failed equations and deferred obligations" $ do
                    let runAt = C.elabExprE (parameter [("x", F.FVar 9)])
                        bad = F.PAnd [F.PAtom F.Ueq (F.EVar "x") zero, equal (F.EVar "x") F.PTrue]
                        inputs = [bad, F.PTrue, equal (F.EVar "x") zero]
                    let forward = map (runAt Nothing) inputs
                        backward = map (runAt Nothing) (reverse inputs)
                    map isRight forward @?= [False, True, True]
                    map isRight backward @?= [True, True, False]
                    case (forward, backward) of
                        ([rejected, _, _], [_, _, rejectedAgain]) -> do
                            assertSortError "Invalid Relation" rejected
                            assertSortError "Invalid Relation" rejectedAgain
                        _ -> assertFailure "the candidate sequence changed"
               , testCase "expected sorts remain per-call constraints" $ do
                    let runAt = C.elabExprE (parameter [("x", F.FVar 9)])
                    map (fmap C.exprSortMaybe . (\sort -> runAt (Just sort) (F.EVar "x"))) [F.FInt, F.boolSort]
                        @?= [Right (Just F.FInt), Right (Just F.boolSort)]
               , testCase "re-elaboration preserves a context-owned type coordinate" $ do
                    let source = F.FVar 44
                        runAt = C.elabExpr (parameter [("identity", F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 0))), ("x", source)]) Nothing
                        first = runAt (F.EApp (F.EVar "identity") (F.EVar "x"))
                    C.exprSortMaybe first @?= Just source
                    runAt first @?= first
                    runAt (runAt first) @?= first
               , testCase "expected coordinates are reserved before fresh instantiation" $ do
                    let runAt = C.elabExprE (parameter [("f", resultScheme)])
                        body = F.ELam ("x", F.FVar 9) (F.PAnd [freshBoolean, equal (F.EVar "x") zero])
                    assertBool "expected coordinate captured" $
                        isRight (runAt (Just (F.FFunc (F.FVar 0) F.boolSort)) body)
               , testCase "theory-only coordinates cannot be reused by fresh occurrences" $ do
                    let ep = parameter [("f", resultScheme)]
                        env = (C.epEnv ep){F.seTheory = F.fromListSEnv [("unused", F.Thy "unused" "unused" (F.FAbs 2 (F.FVar 0)) F.Theory)]}
                        runAt = C.elabExprE ep{C.epEnv = env}
                    case runAt Nothing (F.EApp (F.EVar "f") zero) of
                        Left failure -> assertFailure (show failure)
                        Right output -> do
                            assertBool "theory coordinate reused" (not (S.member 0 (C.sortFieldIndices output)))
                            case C.exprSortMaybe output of
                                Just (F.FVar coordinate) ->
                                    assertBool "result reused a declaration-owned coordinate" (not (S.member coordinate (C.sortFieldIndices env)))
                                result -> assertFailure ("expected a fresh result coordinate, got " ++ show result)
               , testCase "a conditional result cast does not select its branches' source sorts" $ do
                    let ep = parameter [("x", F.FVar 0), ("accept", F.FFunc F.FInt F.boolSort)]
                        conditional = F.ECst (F.EIte F.PTrue (F.EVar "x") zero) F.FReal
                        predicate = F.PAnd [equal conditional (F.ECon (F.R 0)), F.EApp (F.EVar "accept") (F.EVar "x")]
                    assertBool "result coercion changed the branch's source domain" (isRight (C.elabExprE ep Nothing predicate))
               , testCase "local kinds do not mutate the captured outer declaration" $ do
                    let runAt = C.elabExprE (parameter [("alpha", F.FFrac), ("x", F.FObj "alpha")])
                        shadow = F.PAll [("alpha", F.FNum)] (equal (F.EBin F.Mod (F.EVar "x") two) zero)
                        good = equal (F.EBin F.Div (F.EVar "x") two) (F.ECon (F.R 0.5))
                    assertSortError "Operands have different types" (runAt Nothing shadow)
                    assertBool "outer fractional declaration was changed" (isRight (runAt Nothing good))
               , testCase "the negative oracle rejects a panic" $ do
                    outcome <- observe (const (F.panic "negative oracle control")) F.PTrue
                    assertBool "panic counted as a sort rejection" (not (isSortError "Cannot unify" outcome))
               , testCase "the negative oracle rejects unrecognized successful output" $ do
                    outcome <- observe id (F.EVar "unrecognized")
                    outcome @?= Right Nothing
                    assertBool "successful output counted as a sort rejection" (not (isSortError "Cannot unify" outcome))
               ]
            ++ [ testCase (label ++ (if lowerSets then " array-backed" else " native sets") ++ " candidates normalize independently") $ do
                    let elaborateAt = C.elaborate (C.ElabParam (Config.ElabFlags lowerSets False) message F.emptySymEnv)
                        identity sort = F.ELam ("value", sort) (equal (F.EVar "value") (F.ECst (F.EVar "value") sort))
                        bad = F.ELam ("value", source) (F.ECst (F.EVar "value") mismatch)
                    first <- observe elaborateAt (identity source)
                    case first of
                        Right (Just _) -> pure ()
                        _ -> assertFailure ("valid binder normalization failed: " ++ show first)
                    observe elaborateAt bad >>= assertSortError "Cannot cast"
                    observe elaborateAt (identity source) >>= (@?= first)
               | (label, source, mismatch) <- [("set", F.setSort F.FInt, F.setSort F.FReal), ("nested map", F.mapSort F.FInt (F.setSort F.FInt), F.mapSort F.FInt (F.setSort F.FReal))]
               , lowerSets <- [False, True]
               ]

-- Exporting an elaborated predicate must retain the source constructor evidence
-- needed to instantiate its polymorphic applications in a later judgment.
stringRoundTripTests :: TestTree
stringRoundTripTests =
    testGroup "string constructor round trip" $
        [ testCase (quantifierName ++ " " ++ shape) $ do
            let source = quantify [("x", sort)] (nonnegative (F.EApp (F.EVar "len") argument))
                runAt = C.elabExprE (parameter declarations) (Just F.boolSort)
            case runAt source of
                Left failure -> assertFailure (show failure)
                Right elaborated -> do
                    let exported = C.unElab elaborated
                    exported @?= source
                    C.checkSortExpr Nothing F.dummySpan (F.fromListSEnv declarations) exported @?= Just F.boolSort
                    assertBool "exported source predicate cannot be elaborated again" (isRight (runAt exported))
        | (quantifierName, quantify) <- [("exists", F.PExist), ("forall", F.PAll)]
        , (shape, sort, argument) <- [("list", characters, F.EVar "x"), ("nested list", pair characters F.FInt, F.EApp (F.EVar "first") (F.EVar "x"))]
        ]
            ++ [ testCase "native Str does not invent a source constructor" $
                    assertSortError "Cannot unify" $
                        C.elabExprE (parameter declarations) Nothing (F.PExist [("x", F.strSort)] (nonnegative (F.EApp (F.EVar "len") (F.EVar "x"))))
               ]
            ++ [ testCase (show solver ++ " native string length " ++ show valid) $ do
                    let config = Config.defConfig{Config.solver = solver}
                        theory = C.theoryEnv config (mempty :: F.SInfo ())
                        environment = F.symEnv config (F.tsSort <$> theory) theory [] mempty
                        source = F.PAll [("x", characters)] (F.PImp (equal (F.EVar "x") (F.ESym (F.SL "ab"))) (equal (F.EApp (F.EVar "strLen") (F.EVar "x")) (if valid then two else zero)))
                        elaborated = C.elaborate (C.ElabParam (Config.solverFlags config) message environment) source
                    F.sortSmtSort False environment characters @?= F.SString
                    withSMT (SMT.makeContextWithSEnv config "string-round-trip" environment mempty) $ do
                        if solver == Config.Z3 then SMT.smtSetMbqi else pure ()
                        SMT.smtAssert (F.PNot elaborated)
                        response <- SMT.command SMT.CheckSat
                        liftIO (response @?= if valid then SMT.Unsat else SMT.Sat)
               | solver <- [Config.Z3, Config.Cvc5]
               , valid <- [True, False]
               ]
            ++ [ testCase ("exported non-cut solution reused " ++ label ++ " " ++ mode ++ " " ++ show valid) $ do
                    let config = Config.defConfig{Config.eliminate = Config.All, Config.cores = Just 1, Config.sortedSolution = typed}
                        sourceQuery = query source source
                        theory = C.theoryEnv config sourceQuery
                        sourceEnvironment = F.fromListSEnv declarations <> (F.tsSort <$> theory)
                        runAt locals = C.elabExprEAt (Config.solverFlags config) (F.symEnv config sourceEnvironment theory (F.ddecls sourceQuery) mempty) locals message (Just F.boolSort)
                    C.sortExprE Nothing F.dummySpan sourceEnvironment (F.fromListSEnv [("v", F.boolSort)]) source @?= Right F.boolSort
                    first <- Solver.solve config sourceQuery
                    case F.resStatus first of
                        F.Safe _ -> pure ()
                        other -> assertFailure ("source query failed: " ++ show other)
                    case M.lookup kvar (F.resNonCutsSolution first) of
                        Nothing -> assertFailure "the source predicate was not exported as a non-cut solution"
                        Just delayed -> do
                            formal <- case F.resScopes first M.! kvar of
                                [entry] -> pure (F.formalCanonical entry)
                                entries -> assertFailure ("expected one exported formal: " ++ show entries) >> pure F.dummyName
                            let body = F.forceDelayed delayed
                                interface = fmap (map (\formal -> (F.formalCanonical formal, F.formalSort formal))) (M.lookup kvar (F.resScopes first))
                                locals = F.fromListSEnv [(formal, F.boolSort)]
                                actuals = F.fromListSEnv [("v", F.boolSort)]
                                exported = F.substr (S.insert "v" (F.syms body)) (F.mkSubst [(formal, F.EVar "v")]) body
                            interface @?= Just [(formal, F.boolSort)]
                            fmap (map F.formalSource) (M.lookup kvar (F.resScopes first)) @?= Just ["v"]
                            C.sortExprE Nothing F.dummySpan sourceEnvironment locals body @?= Right F.boolSort
                            assertBool "exported interface cannot be elaborated again" (isRight (runAt locals body))
                            C.sortExprE Nothing F.dummySpan sourceEnvironment actuals exported @?= Right F.boolSort
                            assertBool "applied solution cannot be elaborated again" (isRight (runAt actuals exported))
                            forward <- Solver.solve config (query source exported)
                            case F.resStatus forward of
                                F.Safe _ -> pure ()
                                other -> assertFailure ("exported solution strengthened its source: " ++ show other)
                            second <- Solver.solve config (query exported (if valid then source else F.PFalse))
                            case (valid, F.resStatus second) of
                                (True, F.Safe _) -> pure ()
                                (False, F.Unsafe _ failures) -> map fst failures @?= [2]
                                (_, other) -> assertFailure ("reused solution changed the judgment: " ++ show other)
               | (label, source) <-
                    [ ("string", F.PExist [("x", characters)] (nonnegative (F.EApp (F.EVar "len") (F.EVar "x"))))
                    , ("array-backed empty set", F.PNot (F.EApp (F.EApp (F.EVar "arr_select_s") (F.EApp (F.EVar "arr_const_s") F.PFalse)) zero))
                    , ("integer witness cannot equal a fraction", F.POr [F.PExist [("x", F.FInt)] (equal (F.EVar "x") (F.ECon (F.R 0.5))), F.EVar "v"])
                    ]
                        ++ [("source " ++ label ++ " witness", F.PExist [("local", sort)] (F.EApp (F.EVar name) (F.EVar "local"))) | (label, name, sort) <- containers]
                        ++ [("source " ++ label ++ " equality witness", F.PExist [("local", sort)] (F.PAnd [equal (F.EVar "local") (F.EVar (F.suffixSymbol name "Value")), F.EApp (F.EVar name) (F.EVar "local")])) | (label, name, sort) <- containers]
               , (mode, typed) <- [("typed", True), ("display", False)]
               , valid <- [True, False]
               ]
  where
    characters = F.FApp (F.FTC F.listFTyCon) F.charSort
    pair left right = F.fAppTC (F.symbolFTycon (F.dummyLoc "RoundTripPair")) [left, right]
    declarations =
        [ ("len", F.mkFFunc 2 [F.FApp (F.FVar 0) (F.FVar 1), F.FInt])
        , ("first", F.mkFFunc 2 [pair (F.FVar 0) (F.FVar 1), F.FVar 0])
        ]
            ++ [(name, F.FFunc sort F.boolSort) | (_, name, sort) <- containers]
            ++ [(F.suffixSymbol name "Value", sort) | (_, name, sort) <- containers]
    containers =
        [ ("set", "acceptSet", F.setSort F.FInt)
        , ("bag", "acceptBag", F.bagSort F.FInt)
        , ("map", "acceptMap", F.mapSort F.FInt (F.setSort F.FInt))
        , ("datatype", "acceptBox", F.FTC box)
        ]
    box = F.symbolFTycon (F.dummyLoc "ContainerBox")
    nonnegative value = F.PAtom F.Ge value zero
    kvar = F.KV "roundTrip"
    query premise conclusion =
        mempty
            { F.gLits = F.fromListSEnv declarations
            , F.ddecls = [F.DDecl box 0 [F.DCtor (F.dummyLoc "ContainerBox") [F.DField (F.dummyLoc "contents") (F.mapSort F.FInt (F.bagSort (F.setSort F.FInt)))]]]
            , F.ws = M.singleton kvar (F.WfC mempty [("v", F.boolSort)] (kvar) ())
            , F.cm = M.fromList [(1, constraint 1 premise occurrence), (2, constraint 2 occurrence conclusion)]
            }
    occurrence = F.PKVar kvar mempty (F.mkKVarSubst [("v", F.EVar "v")])
    constraint identifier lhs rhs = F.mkSubC mempty (refinement lhs) (refinement rhs) (Just identifier) [] ()
    refinement predicate = F.RR F.boolSort (F.Reft ("v", predicate))

solutionScopeTests :: TestTree
solutionScopeTests =
    testGroup
        "solution presentation owns only its formal telescope"
        [ testCase (label ++ " " ++ show (solver, mode, typed)) $ do
            let config = Config.defConfig{Config.solver = solver, Config.eliminate = mode, Config.cores = Just 1, Config.sortedSolution = typed, Config.noEnvReduction = True, Config.smtMbqi = True}
                names = "vv" : parameters
                locals = F.fromListSEnv [(name, F.FInt) | name <- names]
                declarations = F.fromListSEnv [(name, F.FInt) | name <- globals]
                context = F.fromListIBindEnv [0 .. length parameters - 1]
                occurrence = F.PKVar kvar mempty mempty
                query premise conclusion =
                    mempty
                        { F.bs = F.bindEnvFromList [(i, (name, F.trueSortedReft F.FInt, ())) | (i, name) <- zip [0 ..] parameters]
                        , F.gLits = declarations
                        , F.ws = M.singleton kvar (F.WfC context [("vv", F.FInt)] (kvar) ())
                        , F.quals = [F.mkQ "Source" [(name, F.FInt) | name <- names] source (F.dummyPos "solution-scope")]
                        , F.cm = M.fromList [(1, constraint context 1 premise occurrence), (2, constraint context 2 occurrence conclusion)]
                        }
            first <- Solver.solve config (query source source)
            case F.resStatus first of
                F.Safe _ -> pure ()
                status -> assertFailure ("source relation failed: " ++ show status)
            let formals = F.resScopes first M.! kvar
                canonical = map F.formalCanonical formals
                body = case mode of
                    Config.None -> F.resSolution first M.! kvar
                    _ -> F.forceDelayed (F.resNonCutsSolution first M.! kvar)
                exported = F.subst (F.mkSubst [(F.formalCanonical f, F.EVar (F.formalSource f)) | f <- formals]) body
                formalScope = F.fromListSEnv [(F.formalCanonical f, F.formalSort f) | f <- formals]
                theory = C.theoryEnv config (query source source)
                environment = F.symEnv config (declarations <> (F.tsSort <$> theory)) theory [] mempty
                elaborate scope = C.elabExprEAt (Config.solverFlags config) environment scope message (Just F.boolSort)
            map F.formalSource formals @?= names
            map F.formalSort formals @?= replicate (length names) F.FInt
            S.size (S.fromList canonical) @?= length names
            assertBool "a global became a formal" (all (`notElem` canonical) globals)
            F.syms body `S.difference` S.fromList canonical @?= S.fromList globals
            C.sortExprE Nothing F.dummySpan declarations formalScope body @?= Right F.boolSort
            C.sortExprE Nothing F.dummySpan declarations locals exported @?= Right F.boolSort
            assertBool "exported interface cannot be elaborated" (isRight (elaborate formalScope body))
            assertBool "applied solution cannot be elaborated" (isRight (elaborate locals exported))
            mapM_
                ( \(premise, conclusion, valid) -> do
                    result <- Solver.solve config (query premise conclusion)
                    case (valid, F.resStatus result) of
                        (True, F.Safe _) -> pure ()
                        (False, F.Unsafe _ failures) -> map fst failures @?= [2]
                        (_, status) -> assertFailure ("readback changed the relation: " ++ show status)
                )
                [(source, exported, True), (exported, source, True), (exported, F.PFalse, False)]
        | solver <- [Config.Z3, Config.Cvc5]
        , mode <- [Config.None, Config.All]
        , typed <- [False, True]
        , (label, parameters, globals, source) <-
            [ ("fixed global collides with pretty formal", ["x"], ["$x"], relation "$x")
            , ("distinct formals have identical pretty names", ["x", "nnf_arg$x"], [], relation "nnf_arg$x")
            , ("global resembles an internal formal", ["x"], ["lq_karg$fixed##scope"], relation "lq_karg$fixed##scope")
            , ("lexical binder collides with pretty formal", ["x"], [], F.PExist [("$x", F.FInt)] (F.PAnd [relation "$x", F.PAtom F.Ge (F.EVar "$x") zero]))
            ]
        ]
  where
    kvar = F.KV "scope"
    relation right = equal (F.EVar "vv") (F.EBin F.Plus (F.EVar "x") (F.EVar right))
    constraint context identifier lhs rhs = F.mkSubC context (refinement lhs) (refinement rhs) (Just identifier) [] ()
    refinement predicate = F.RR F.FInt (F.Reft ("vv", predicate))

binderRepresentationTests :: TestTree
binderRepresentationTests =
    testGroup "source binder representation" $
        [ testCase (binderName ++ " " ++ shape) $ do
            let source = bind [("f", sourceSort)] body
                exported = C.unElab (C.elaborate (parameter []) source)
            exported @?= source
            C.checkSortExpr Nothing F.dummySpan mempty exported @?= C.checkSortExpr Nothing F.dummySpan mempty source
            assertBool "exported binder cannot be elaborated again" (isRight (C.elabExprE (parameter []) Nothing exported))
        | (binderName, bind) <- [("exists", F.PExist), ("forall", F.PAll), ("lambda", flip (foldr F.ELam))]
        , (shape, sourceSort, body) <-
            [ ("arrow", arrow, equal (F.EApp (F.EVar "f") F.PTrue) zero)
            , ("datatype named function", nominal, equal (F.EVar "f") (F.EVar "f"))
            ]
        ]
            ++ [ testCase ("source Set and Array remain distinct " ++ show lowerSets) $ do
                    let source = F.setSort F.FInt
                        encoded = F.arraySort F.FInt F.boolSort
                        ep = (parameter [("set", source), ("array", encoded), ("accept", F.FFunc source F.boolSort)]){C.epFlags = Config.ElabFlags lowerSets False}
                        check = C.elabExprE ep Nothing
                    assertBool "a source application accepted an encoded carrier" (not (isRight (check (F.EApp (F.EVar "accept") (F.EVar "array")))))
                    assertBool "a source cast accepted an encoded carrier" (not (isRight (check (F.ECst (F.EVar "set") encoded))))
                    assertBool "source equality accepted an encoded carrier" (not (isRight (check (equal (F.EVar "set") (F.EVar "array")))))
                    isRight (check (F.PAtom F.Ueq (F.EVar "set") (F.EVar "array"))) @?= lowerSets
               | lowerSets <- [False, True]
               ]
            ++ [ testCase "a datatype named function cannot capture an arrow carrier" $ do
                    let datatype = F.DDecl constructor 2 [F.DCtor (F.dummyLoc "FunctionData") [F.DField (F.dummyLoc "domain") (F.FVar 0), F.DField (F.dummyLoc "range") (F.FVar 1)]]
                        environment = F.emptySymEnv{F.seData = F.fromListSEnv [("function", datatype)]}
                        elaborateSort = C.elaborate (parameter []){C.epEnv = environment}
                    F.sortSmtSort False environment (elaborateSort arrow) @?= F.SInt
                    F.sortSmtSort False environment (elaborateSort nominal) @?= F.SData constructor [F.SBool, F.SInt]
               ]
            ++ [ testCase (show solver ++ " PLE function witness " ++ show valid) $ do
                    let config = Config.defConfig{Config.solver = solver, Config.allowHO = True, Config.cores = Just 1, Config.rewriteAxioms = True}
                        query = witnessQuery valid
                    initial <- Solver.solve config{Config.rewriteAxioms = False} query
                    case F.resStatus initial of
                        F.Unsafe _ failures -> map fst failures @?= [1]
                        other -> assertFailure ("the fixture did not require PLE: " ++ show other)
                    result <- Solver.solve config query
                    case (valid, F.resStatus result) of
                        (True, F.Safe _) -> pure ()
                        (False, F.Unsafe _ failures) -> map fst failures @?= [1]
                        (_, other) -> assertFailure ("function witness changed meaning: " ++ show other)
               | solver <- [Config.Z3, Config.Cvc5]
               , valid <- [True, False]
               ]
  where
    arrow = F.FFunc F.boolSort F.FInt
    constructor = F.symbolFTycon (F.dummyLoc "function")
    nominal = F.fAppTC constructor [F.boolSort, F.FInt]
    witnessQuery valid =
        mempty
            { F.gLits = F.fromListSEnv [("observeCallback", F.FFunc arrow F.FInt)]
            , F.hoInfo = F.HOI True False
            , F.cm = M.singleton 1 (F.mkSubC mempty (refinement premise) (refinement conclusion) (Just 1) [] ())
            , F.ae = mempty{F.aenvEqs = [equation], F.aenvExpand = M.singleton 1 True}
            }
      where
        equation = F.Equ "observeCallback" [("callback", arrow)] (F.EApp (F.EVar "callback") F.PTrue) F.FInt False
        premise = F.PExist [("f", arrow)] (F.PAnd [equal (F.EApp (F.EVar "f") F.PTrue) two, equal (F.EVar "v") (F.EApp (F.EVar "observeCallback") (F.EVar "f"))])
        conclusion = equal (F.EVar "v") (if valid then two else zero)
        refinement predicate = F.RR F.FInt (F.Reft ("v", predicate))

suffixCandidateTests :: TestTree
suffixCandidateTests =
    testGroup
        "text suffix factoring preserves the original candidate stream"
        ( [ testCase (T.unpack spelling) $ do
                let input = F.symbol spelling
                    original = originalCandidates input
                    observe name = (F.symbolText name, F.symbolSafeText name, F.symbolSmtText name)
                    scopes = [S.empty, S.singleton input, S.fromList (take 8 original), S.fromList [original !! i | i <- [0, 2, 4, 6]]]
                map observe (take 32 (F.candidates input)) @?= map observe (take 32 original)
                mapM_
                    ( \scope -> do
                        F.freshInNS input scope @?= originalFresh input scope
                        F.freshInNSL (replicate 6 input) scope @?= mapAccumL (flip originalFresh) scope (replicate 6 input)
                    )
                    scopes
          | spelling <-
                [ "source"
                , "source##"
                , "source##not-number"
                , "source##0"
                , "source##-2"
                , "source##+2"
                , "source## 2"
                , "source##2 "
                , "source##(2)"
                , "source##0002"
                , "##2"
                , "source##nested##2"
                , "λ雪##2"
                , "λ雪##not-number"
                , "source##" <> T.pack (show (toInteger (maxBound :: Int)))
                , "source##" <> T.pack (show (toInteger (maxBound :: Int) + 100000000000000000000))
                ]
          ]
            ++ [ testCase "the unchanged first candidate does not demand suffix preparation" $ do
                    evaluate (length (take 1 (F.candidates (error "suffix preparation forced the input" :: F.Symbol)))) >>= (@?= 1)
                    evaluate (length (take 0 (F.candidates (error "zero-prefix demand forced the input" :: F.Symbol)))) >>= (@?= 0)
               ]
        )
  where
    originalCandidates input =
        let (base, start) = split input
         in input : map (F.intSymbol base) [start ..]
    split input =
        case T.breakOnEnd F.symSepName (F.symbolText input) of
            (prefix, suffix)
                | T.null prefix -> (input, 0 :: Integer)
                | otherwise -> case reads (T.unpack suffix) of
                    ((index, []) : _) -> (F.unSuffixSymbol input, index + 1 :: Integer)
                    _ -> (input, 0 :: Integer)
    originalFresh input scope =
        let chosen = head (filter (not . (`S.member` scope)) (originalCandidates input))
         in (S.insert chosen scope, chosen)

fresheningTests :: TestTree
fresheningTests =
    testGroup
        "shared nominal freshening"
        [ suffixCandidateTests
        , testGroup
            "suffix allocation remains fresh beyond bounded Int"
            [ testCase (show boundary) $ do
                let candidate = F.intSymbol "source" boundary
                    occupied = S.fromList [candidate, F.intSymbol "source" (boundary + 1)]
                    (inside, chosen) = F.freshInNS candidate occupied
                chosen @?= F.intSymbol "source" (boundary + 2)
                inside @?= S.insert chosen occupied
            | boundary <- [toInteger (maxBound :: Int) - 1, toInteger (maxBound :: Int)]
            ]
        , testCase "two allocations extend the same finite namespace" $ do
            let candidate = F.intSymbol "source" (0 :: Integer)
                occupied = S.fromList [candidate, F.intSymbol "source" (1 :: Integer)]
                (firstScope, first) = F.freshInNS candidate occupied
                (secondScope, second) = F.freshInNS candidate firstScope
            assertBool "allocation captured an occupied name" (not (S.member first occupied) && not (S.member second occupied))
            assertBool "allocations share a name" (first /= second)
            secondScope @?= S.insert second (S.insert first occupied)
        , testCase "colliding KVar formals preserve both source actuals and source patterns" $ do
            let first = F.KV "shared##0"
                second = F.KV "shared##1"
                occupied = F.kArgSymbol "x" (F.kv first)
                scope = F.fromListIBindEnv [0]
                occurrence variable = F.PKVar variable mempty (F.mkKVarSubst [("x", F.EVar "x")])
                input =
                    (mempty :: F.SInfo ())
                        { F.bs = F.bindEnvFromList [(0, ("x", F.trueSortedReft F.FInt, ()))]
                        , F.gLits = F.fromListSEnv [(occupied, F.boolSort)]
                        , F.ws = M.fromList [(variable, F.WfC scope [("v", F.boolSort)] (variable) ()) | variable <- [first, second]]
                        , F.cm = M.singleton 1 (F.SimpC scope (F.PAnd (map occurrence [first, second])) (Just 1) 0 [] ())
                        }
                (origins, processed) = KVars.wfcUniqify input
                formal variable =
                    case [name | KVars.BindOrigin "x" identifier <- M.lookupDefault [] variable origins, let (name, _, _) = F.lookupBindEnv identifier (F.bs processed)] of
                        [name] -> pure name
                        names -> assertFailure ("missing source formal: " ++ show names) >> pure F.dummyName
            names <- mapM formal [first, second]
            assertBool "generated formals captured declarations or each other" (occupied `notElem` names && S.size (S.fromList names) == 2)
            map F.unKArgSymbol names @?= ["x", "x"]
            let actuals (variable, name) =
                    [ value
                    | constraint <- M.elems (F.cm processed)
                    , substitution <- M.lookupDefault [] variable (F.exprKVars (F.crhs constraint))
                    , Just value <- [M.lookup name (F.fromKVarSubst substitution)]
                    ]
            map actuals (zip [first, second] names) @?= [[F.EVar "x"], [F.EVar "x"]]
        ]

constraintTests :: TestTree
constraintTests =
    testGroup
        "prepared constraint elaboration"
        [ testCase "failures retain each constraint's exact location and predicate text" $ do
            let elaborateAt = C.elaborate (parameter [])
            mapM_
                ( \identifier -> do
                    let position = F.safeSourcePos "constraint-errors.hs" (fromInteger identifier) 1
                        location = F.SS position position
                        predicate = equal (F.EVar "missing_symbol") (F.ECon (F.I identifier))
                        expected =
                            "elaborate prepared elaboration failed on:\n    missing_symbol == "
                                ++ show identifier
                                ++ "\nwith error\n    Unbound symbol missing_symbol --- perhaps you meant:  ?\nin environment"
                    outcome <- observe (F._crhs . elaborateAt . constraint identifier location) predicate
                    case outcome of
                        Left failure -> [(F.errLoc diagnostic, show (F.errMsg diagnostic)) | diagnostic <- F.errs failure] @?= [(location, expected)]
                        Right _ -> assertFailure "constraint with an unknown symbol was accepted"
                )
                [17, 43, 17]
        , testCase "constraint judgments reset successful and failed polymorphic equations" $ do
            let elaborateAt = C.elaborate (parameter [("f", F.FVar 9)])
                inputs = [integerCall, booleanCall, F.PAnd [integerCall, booleanCall], booleanCall, integerCall]
            outcomes <- mapM (\(identifier, predicate) -> observe (F._crhs . elaborateAt . constraint identifier F.dummySpan) predicate) (zip [1 ..] inputs)
            case outcomes of
                [first, second, rejected, fourth, fifth] -> do
                    [first, second, fourth, fifth] @?= replicate 4 (Right (Just F.boolSort))
                    assertSortError "Cannot unify" rejected
                _ -> assertFailure "the constraint sequence changed"
        , testCase "constraint RHSs must still have the expected Bool sort" $
            observe (F._crhs . C.elaborate (parameter []) . constraint 1 F.dummySpan) zero >>= assertSortError "Cannot unify"
        ]
  where
    constraint :: Integer -> F.SrcSpan -> F.Expr -> F.SimpC F.SrcSpan
    constraint identifier location predicate = F.SimpC F.emptyIBindEnv predicate (Just identifier) 0 [] location

refinementTests :: TestTree
refinementTests =
    testGroup
        "prepared refinement elaboration"
        [ testCase "source carriers and predicate casts survive the lexical binder" $
            mapM_
                ( \(ef, source, predicate) -> do
                    let ep = (parameter []){C.epFlags = ef}
                        input = F.RR source (F.Reft ("value", predicate))
                        bodyParameter = ep{C.epEnv = F.insertSymEnv "value" source F.emptySymEnv}
                        expected = F.RR source (F.Reft ("value", C.elaborate bodyParameter predicate))
                    C.elaborate ep input @?= expected
                )
                [ (Config.ElabFlags lowerSets False, source, predicate)
                | lowerSets <- [False, True]
                , (source, predicate) <-
                    [ (source, equal (F.EVar "value") (F.ECst (F.EVar "value") source))
                    | source <- [F.FInt, F.setSort F.FInt, F.mapSort F.FInt (F.setSort F.FInt), F.FFunc F.FInt F.boolSort]
                    ]
                        ++ [(F.boolSort, F.ECst (F.EVar "value") F.boolSort), (F.FFunc F.FInt F.boolSort, F.EApp (F.EVar "value") zero)]
                ]
        , testCase "expected Bool still solves an unresolved predicate sort" $
            C.elaborate (parameter []) (F.RR (F.FVar 9) (F.Reft ("value", F.EVar "value")))
                @?= F.RR (F.FVar 9) (F.Reft ("value", F.ECst (F.EVar "value") F.boolSort))
        , testCase "false predicates remain false and non-Boolean predicates are rejected" $ do
            let elaborateAt = predicateOf . C.elaborate (parameter []) . refinement
            elaborateAt F.PFalse @?= F.PFalse
            observe elaborateAt zero >>= assertSortError "Cannot unify"
        , testCase "refinement judgments reset successful and failed inference" $ do
            let elaborateAt = predicateOf . C.elaborate (parameter [("f", F.FVar 9)]) . refinement
            outcomes <- mapM (observe elaborateAt) [integerCall, booleanCall, F.PAnd [integerCall, booleanCall], booleanCall, integerCall]
            case outcomes of
                [first, second, rejected, fourth, fifth] -> do
                    [first, second, fourth, fifth] @?= replicate 4 (Right (Just F.boolSort))
                    assertSortError "Cannot unify" rejected
                _ -> assertFailure "the refinement sequence changed"
        , testCase "source alias scoping retains implicit KVar actuals" $ do
            let ep = parameter [("alpha", F.FFrac), ("outer", F.FObj "alpha")]
                occurrence = F.PKVar (F.KV "scoped") mempty mempty
                input = F.RR (F.FObj "alpha") (F.Reft ("alpha", occurrence))
            case C.elaborate ep input of
                F.RR source (F.Reft (value, F.PKVar _ _ actuals)) -> do
                    source @?= F.FReal
                    value @?= "alpha"
                    F.fromKVarSubst actuals @?= M.empty
                other -> assertFailure (show other)
        , testCase "only ambient declarations supply nominal type equality" $ do
            let body = F.ECon (F.L "literal" (F.FObj "value"))
                input = F.RR F.boolSort (F.Reft ("value", body))
                elaborateAt ep predicate = predicateOf (C.elaborate ep (F.RR F.boolSort (F.Reft ("value", predicate))))
            predicateOf (C.elaborate (parameter [("value", F.boolSort)]) input) @?= body
            observe (elaborateAt (parameter [])) body >>= assertSortError "Cannot unify"
        , testCase "initial lexical telescopes mask native function declarations" $ do
            let name = "bool_to_int"
                arrow = F.FFunc F.boolSort F.FInt
                plain = parameter []
                decorated = plain{C.epEnv = F.emptySymEnv{F.seSort = F.fromListSEnv [(name, arrow)], F.seTheory = F.fromListSEnv [(name, F.Thy name "bool_to_int" arrow F.Theory)]}}
                application = F.EApp (F.EVar name) F.PTrue
                refinement = F.RR arrow (F.Reft (name, equal application zero))
                equation = F.Equ "localCallable" [(name, arrow)] application F.FInt False
            C.elaborate decorated refinement @?= C.elaborate plain refinement
            C.elaborate decorated equation @?= C.elaborate plain equation
            C.elaborate decorated (F.MkDefinedFuns [equation]) @?= C.elaborate plain (F.MkDefinedFuns [equation])
            assertBool "parameter application acquired native meaning" $
                S.member F.applyName (F.syms (F.eqBody (C.elaborate decorated equation)))
        , testCase "an equation telescope retains its first duplicate binding" $ do
            let equation = F.Equ "duplicateParameter" [("x", F.boolSort), ("x", F.FInt)] (F.EVar "x") F.boolSort False
                F.MkDefinedFuns [result] = C.elaborate (parameter []) (F.MkDefinedFuns [equation])
            C.exprSortMaybe (F.eqBody result) @?= Just F.boolSort
            map fst (F.eqArgs result) @?= ["x", "x"]
        , testCase "post-elaboration Bool validation solves a fresh polymorphic result" $
            C.elaborate (parameter [("poly", F.FAbs 0 (F.FVar 0))]) (refinement (F.EVar "poly"))
                @?= refinement (F.ECst (F.EVar "poly") F.boolSort)
        , testCase "binding failures retain the row's diagnostic location" $
            mapM_
                ( \identifier -> do
                    let position = F.safeSourcePos "refinement-errors.hs" identifier 1
                        location = F.SS position position
                        input = F.bindEnvFromList [(identifier, ("binding", refinement (equal (F.EVar "missing_symbol") zero), location))]
                    outcome <- try (evaluate (force (C.elaborate (parameter []) input))) :: IO (Either F.Error (F.BindEnv F.SrcSpan))
                    case outcome of
                        Left failure -> do
                            map F.errLoc (F.errs failure) @?= [location]
                            assertBool "binding diagnostic lost its owner" $
                                any (isInfixOf ("elabBE " ++ show identifier) . show . F.errMsg) (F.errs failure)
                        Right _ -> assertFailure "binding with an unknown symbol was accepted"
                )
                [17, 43]
        ]
  where
    refinement predicate = F.RR F.FInt (F.Reft ("value", predicate))
    predicateOf = F.reftPred . F.sr_reft

inferenceTests :: TestTree
inferenceTests =
    testGroup
        "prepared sort inference"
        [ testCase "lexical telescopes do not supply nominal equality aliases" $ do
            let locals = F.fromListSEnv [("alpha", F.boolSort)]
                predicate = equal (F.ECon (F.L "nominal" (F.FObj "alpha"))) F.PTrue
                declarations = F.fromListSEnv [("alpha", F.FVar 9)]
                inferAt ambient = C.sortExprE Nothing F.dummySpan ambient locals predicate
            map (isRight . inferAt) [mempty, declarations, mempty] @?= [False, True, False]
            observe (\body -> C.elaborateExpr flags F.emptySymEnv locals message body (Just F.boolSort)) predicate >>= assertSortError "Cannot unify"
        , testCase "lexical annotations close against declarations, not sibling term bindings" $ do
            let declarations = F.fromListSEnv [("alpha", F.FFrac)]
                locals = F.fromListSEnv [("alpha", F.FNum), ("x", F.FObj "alpha")]
            C.sortExprE Nothing F.dummySpan declarations locals (F.EVar "x") @?= Right F.FReal
            assertBool "lexical kind changed fractional arithmetic" $
                not (isRight (C.sortExprE Nothing F.dummySpan declarations locals (F.EBin F.Mod (F.EVar "x") two)))
        , testCase "shared inference declarations keep changing lexical judgments independent" $ do
            let declarations = F.fromListSEnv [("f", F.FVar 9), ("x", F.FInt)]
                inferAt = C.sortExprE Nothing F.dummySpan declarations
                locals sort index = F.fromListSEnv [("x", sort), ("coordinate", F.FVar index)]
                predicate call value coordinate = F.PAnd [call, equal (F.EVar "x") value, equal (F.EVar "coordinate") coordinate]
                boolean = predicate booleanCall F.PTrue zero
                integer = predicate integerCall zero F.PTrue
                cases =
                    [ (locals F.boolSort 0, boolean)
                    , (locals F.FInt 1, boolean)
                    , (locals F.FInt 1, integer)
                    , (locals F.boolSort 0, boolean)
                    ]
                outcomes = [inferAt local body | (local, body) <- cases]
            map (either (const Nothing) Just) outcomes @?= [Just F.boolSort, Nothing, Just F.boolSort, Just F.boolSort]
        , testCase "joint let judgment reserves lexical annotation coordinates" $ do
            let declarations = F.fromListSEnv [("make", F.FAbs 7 (F.FFunc F.FInt (F.FVar 7)))]
                locals = F.fromListSEnv [("local", F.FVar 0)]
            case jointSorts declarations locals [F.EApp (F.EVar "make") zero, F.EVar "local"] of
                Right [F.FVar fresh, F.FVar retained] -> do
                    assertBool "opened scheme captured a lexical coordinate" (fresh /= 0)
                    retained @?= 0
                other -> assertFailure (show other)
        , testCase "successful and failed single-expression judgments remain independent" $ do
            let environment = F.fromListSEnv [("f", F.FVar 9)]
                inferAt = C.sortExpr Nothing F.dummySpan environment
                checkAt = C.checkSortExpr Nothing F.dummySpan environment
                inputs = [integerCall, booleanCall, F.PAnd [integerCall, booleanCall], booleanCall, integerCall]
                expected = [Just F.boolSort, Just F.boolSort, Nothing, Just F.boolSort, Just F.boolSort]
            outcomes <- mapM (try . evaluate . force . inferAt) inputs :: IO [Either F.Error F.Sort]
            map (either (const Nothing) Just) outcomes @?= expected
            map checkAt inputs @?= expected
            case outcomes of
                [_, _, Left failure, _, _] ->
                    assertBool "the joint expression did not report conflicting sort equations" $
                        any (isInfixOf "Cannot unify" . show . F.errMsg) (F.errs failure)
                _ -> assertFailure "the inference sequence changed"
        , testCase "sortExpr retains exact error ownership and text" $
            mapM_
                ( \identifier -> do
                    let position = F.safeSourcePos "inference-errors.hs" (fromInteger identifier) 1
                        location = F.SS position position
                        predicate = equal (F.EVar "missing_symbol") (F.ECon (F.I identifier))
                        expected =
                            "sortExpr failed on expression:\n    missing_symbol == "
                                ++ show identifier
                                ++ "\nwith error:\n    Unbound symbol missing_symbol --- perhaps you meant:  ?\nin environment"
                    outcome <- try (evaluate (force (C.sortExpr Nothing location mempty predicate))) :: IO (Either F.Error F.Sort)
                    case outcome of
                        Left failure -> [(F.errLoc diagnostic, show (F.errMsg diagnostic)) | diagnostic <- F.errs failure] @?= [(location, expected)]
                        Right _ -> assertFailure "inference accepted an unknown symbol"
                )
                [17, 43]
        ]

relationalSetTests :: TestTree
relationalSetTests =
    testGroup
        "relational set candidates"
        [ testCase (show solver ++ if good then " emptiness" else " false complement") $ do
            result <- Solver.solve Config.defConfig{Config.solver = solver, Config.eliminate = Config.None, Config.cores = Just 1} (relationalSetQuery good)
            case (good, F.resStatus result) of
                (True, F.Safe _) -> pure ()
                (False, F.Unsafe _ failures) -> map fst failures @?= [2]
                _ -> assertFailure (show (F.resStatus result))
        | solver <- [Config.Z3, Config.Cvc5]
        , good <- [True, False]
        ]

-- The composition contract needs to infer this relation at a cut KVar.
-- Its Set formal and the qualifier must share the backend's interpretation.
relationalSetQuery :: Bool -> F.FInfo ()
relationalSetQuery good =
    mempty
        { F.bs = F.bindEnvFromList [(0, ("xs", F.trueSortedReft (F.setSort F.FInt), ()))]
        , F.gLits = F.fromListSEnv [("Set_emp", F.FAbs 0 (F.FFunc (F.setSort (F.FVar 0)) F.boolSort))]
        , F.ws = M.singleton kvar (F.WfC environment [("v", F.boolSort)] (kvar) ())
        , F.quals = [F.mkQ "Empty" [("v", F.boolSort), ("xs", F.setSort F.FInt)] predicate (F.dummyPos "composition")]
        , F.cm = M.fromList [(1, constraint 1 predicate occurrence), (2, constraint 2 occurrence (if good then predicate else F.PNot predicate))]
        }
  where
    kvar = F.KV "relation"
    environment = F.fromListIBindEnv [0]
    predicate = F.PIff (F.EVar "v") (F.EApp (F.EVar "Set_emp") (F.EVar "xs"))
    occurrence = F.PKVar kvar mempty (F.mkKVarSubst [("v", F.EVar "v"), ("xs", F.EVar "xs")])
    refinement p = F.RR F.boolSort (F.Reft ("v", p))
    constraint identifier lhs rhs = F.mkSubC environment (refinement lhs) (refinement rhs) (Just identifier) [] ()

querySortTests :: TestTree
querySortTests =
    testGroup
        "query candidate source sorts"
        [ testCase (label ++ if lowerSets then " array-backed" else " native sets") $ do
            let ef = Config.ElabFlags lowerSets False
                cfg = Config.defConfig{Config.solver = if lowerSets then Config.Z3 else Config.Cvc5}
                ep = C.ElabParam ef message F.emptySymEnv
                kvar = F.KV "candidate"
                environment = F.fromListIBindEnv [0]
                qualifier = F.mkQ "Same" [("v", source), ("x", source)] (equal (F.ECst (F.EVar "v") source) (F.EVar "x")) (F.dummyPos "candidate")
                input =
                    mempty
                        { F.bs = F.bindEnvFromList [(0, ("x", F.trueSortedReft source, ()))]
                        , F.ws = M.singleton kvar (F.WfC environment [("v", source)] (kvar) ())
                        , F.quals = [qualifier]
                        } ::
                        F.SInfo ()
                output = C.elaborate ep input
                expected = source
                actual = F.wvvs (F.ws output M.! kvar)
                instantiated = Solution.init cfg output (S.singleton kvar)
            actual @?= [("v", expected)]
            case F.quals output of
                [loweredQualifier] -> do
                    map F.qpSort (F.qParams loweredQualifier) @?= [expected, expected]
                    F.qBody loweredQualifier @?= F.qBody qualifier
                _ -> assertFailure "qualifier inventory changed"
            case M.lookup kvar instantiated of
                Just (Sol.QB candidates) -> assertBool "valid equality candidate was lost" (not (null candidates))
                Nothing -> assertFailure "candidate owner disappeared"
            C.elaborate ep (F.PKVar kvar (M.singleton "a" source) mempty :: F.Expr)
                @?= F.PKVar kvar (M.singleton "a" expected) mempty
            C.elaborate ep (F.PKVar kvar (M.singleton "f" (F.FFunc source source)) mempty :: F.Expr)
                @?= F.PKVar kvar (M.singleton "f" (F.FFunc expected expected)) mempty
            let actual sort = F.PExist [("x", sort)] (equal (F.ECst (F.EVar "x") sort) (F.EVar "x"))
                occurrence sort = F.PKVar kvar (M.singleton "a" sort) (F.mkKVarSubst [("argument", actual sort)])
            C.elaborate ep (occurrence source) @?= occurrence expected
        | (label, source) <- [("set", F.setSort F.FInt), ("bag", F.bagSort F.FInt), ("nested map", F.mapSort F.FInt (F.setSort F.FInt))]
        , lowerSets <- [False, True]
        ]

closureWhnfTests :: TestTree
closureWhnfTests =
    testGroup
        "partial-application demand"
        [ testCase "elaborate closure does not demand its parameter" $
            evaluate ((C.elaborate missingParameter :: F.Expr -> F.Expr) `seq` ())
        , testCase "constraint elaboration closure does not demand its parameter" $
            evaluate ((C.elaborate missingParameter :: F.SimpC F.SrcSpan -> F.SimpC F.SrcSpan) `seq` ())
        , testCase "refinement elaboration closure does not demand its parameter" $
            evaluate ((C.elaborate missingParameter :: F.SortedReft -> F.SortedReft) `seq` ())
        , testCase "binding elaboration closure does not demand its parameter" $
            evaluate ((C.elaborate missingParameter :: F.BindEnv F.SrcSpan -> F.BindEnv F.SrcSpan) `seq` ())
        , testCase "elabExpr closure does not demand its parameter" $
            evaluate (C.elabExpr missingParameter `seq` ())
        , testCase "elabExprE closure does not demand its parameter" $
            evaluate (C.elabExprE missingParameter `seq` ())
        , testCase "elabExpr partial call does not demand expected sort" $
            evaluate (C.elabExpr missingParameter missingExpected `seq` ())
        , testCase "elabExprE partial call does not demand expected sort" $
            evaluate (C.elabExprE missingParameter missingExpected `seq` ())
        , testCase "sortExpr partial call does not demand its location or environment" $
            evaluate (C.sortExpr Nothing missingLocation missingEnvironment `seq` ())
        , testCase "checkSortExpr partial call does not demand its location or environment" $
            evaluate (C.checkSortExpr Nothing missingLocation missingEnvironment `seq` ())
        ]
  where
    missingParameter = error "partial elaboration demanded its parameter"
    missingExpected = error "partial elaboration demanded its expected sort"
    missingLocation = error "partial inference demanded its location"
    missingEnvironment = error "partial inference demanded its environment"

observe :: (F.Expr -> F.Expr) -> F.Expr -> IO (Either F.Error (Maybe F.Sort))
observe elaborateAt input = do
    outcome <- try (evaluate (force (elaborateAt input))) :: IO (Either F.Error F.Expr)
    pure (outputSort <$> outcome)

assertSortError :: (Show a) => String -> Either F.Error a -> IO ()
assertSortError category outcome =
    assertBool ("expected " ++ category ++ " sort rejection, got " ++ show outcome) (isSortError category outcome)

-- LF panics use Error too. Require the existing elaboration diagnostic and
-- intended sort-error category, never an arbitrary exception or lost output.
isSortError :: String -> Either F.Error a -> Bool
isSortError category (Left failure) = case F.errs failure of
    [diagnostic] ->
        let text = show (F.errMsg diagnostic)
         in F.errLoc diagnostic == F.dummySpan
                && "elaborate prepared elaboration failed on:" `isPrefixOf` text
                && category `isInfixOf` text
                && not ("PANIC:" `isInfixOf` text)
    _ -> False
isSortError _ (Right _) = False

outputSort :: F.Expr -> Maybe F.Sort
outputSort (F.PAtom F.Eq left right)
    | Just leftSort <- C.exprSortMaybe left
    , Just rightSort <- C.exprSortMaybe right
    , leftSort == rightSort =
        Just F.boolSort
outputSort (F.PAnd predicates)
    | all ((== Just F.boolSort) . outputSort) predicates = Just F.boolSort
outputSort expression = C.exprSortMaybe expression

parameter :: [(F.Symbol, F.Sort)] -> C.ElabParam
parameter declarations = C.ElabParam flags message F.emptySymEnv{F.seSort = F.fromListSEnv declarations}

message :: F.Located String
message = F.atLoc F.dummySpan "prepared elaboration"

flags :: Config.ElabFlags
flags = Config.ElabFlags True False

zero, two, integerCall, booleanCall, freshBoolean :: F.Expr
zero = F.ECon (F.I 0)
two = F.ECon (F.I 2)
integerCall = equal (F.EApp (F.EVar "f") zero) zero
booleanCall = equal (F.EApp (F.EVar "f") F.PTrue) F.PTrue
freshBoolean = equal (F.EApp (F.EVar "f") zero) F.PTrue

equal :: F.Expr -> F.Expr -> F.Expr
equal = F.PAtom F.Eq

resultScheme :: F.Sort
resultScheme = F.FAbs 42 (F.FFunc F.FInt (F.FVar 42))
