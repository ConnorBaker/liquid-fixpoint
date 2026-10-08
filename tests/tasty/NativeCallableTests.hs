{-# LANGUAGE OverloadedStrings #-}

module NativeCallableTests (tests, withSMT) where

import Control.Exception (bracket)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (StateT, evalStateT, execState)
import qualified Data.HashMap.Strict as M
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Theories as Theory
import qualified Language.Fixpoint.SortCheck as So
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types.Visitor as V
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "escaping native function values"
        [ testCase "Boolean callback retains its operation" $ check C.Z3 False (@?= SMT.Unsat) booleanGood
        , testCase "Boolean callback false law has a model" $ check C.Z3 False (@?= SMT.Sat) booleanBad
        , testCase "finite array callback retains selection" $ check C.Z3 False (@?= SMT.Unsat) arrayGood
        , testCase "native declarations and equations follow push and pop" $ check C.Z3 True (@?= SMT.Unsat) booleanGood
        , testCase "indexed SMT operators retain their syntax" $ check C.Z3 False (@?= SMT.Unsat) indexedGood
        , testCase "native value names cannot capture a lexical binder" $
            check
                C.Z3
                False
                (@?= SMT.Unsat)
                (F.PAll [(F.intSymbol "lq_instantiated_value" (0 :: Int), F.boolSort)] booleanGood)
        , testCase "application itself can escape as a native value" $
            check C.Z3 False (@?= SMT.Unsat) applicationGood
        , polymorphicOccurrenceTests
        , phantomDatatypeTests
        , opaqueConstantTests
        , collectionTests
        , cardinalityTests
        , testGroup
            "quantified array model incompleteness is not a proof"
            [ testCase (show solver) $ check solver False notProved arrayBad
            | solver <- [C.Z3, C.Cvc5]
            ]
        ]
  where
    notProved response =
        assertBool
            ("false law returned " ++ show response)
            (response == SMT.Sat || response == SMT.Unknown)

-- An unused type parameter does not add an inhabitant to a datatype.
-- Observe two distinct instances through the actual elaborator and serializer;
-- satisfiable false laws ensure that coverage is not obtained by inconsistency.
phantomDatatypeTests :: TestTree
phantomDatatypeTests =
    testGroup
        "phantom datatype constructor coverage"
        [ testCase (show solver ++ " " ++ label) $ query solver predicate expected
        | solver <- [C.Z3, C.Cvc5]
        , (label, predicate, expected) <-
            [ ("enum instances contain exactly their constructors", F.PNot (F.PAnd enumCoverage), SMT.Unsat)
            , ("enum instances need not select the first constructor", F.PNot (F.PAnd enumFirst), SMT.Sat)
            , ("payload instances reconstruct from their only constructor", F.PNot (F.PAnd payloadCoverage), SMT.Unsat)
            , ("payload instances need not carry zero", F.PNot (F.PAnd payloadZero), SMT.Sat)
            ]
        ]
  where
    enumTycon = F.symbolFTycon (F.dummyLoc "PhantomEnum")
    payloadTycon = F.symbolFTycon (F.dummyLoc "PhantomPayload")
    declarations =
        [ F.DDecl enumTycon 1 [F.DCtor (F.dummyLoc "PhantomFirst") [], F.DCtor (F.dummyLoc "PhantomSecond") []]
        , F.DDecl payloadTycon 1 [F.DCtor (F.dummyLoc "PhantomValue") [F.DField (F.dummyLoc "phantomValue") F.FInt]]
        ]
    instances tycon names = zipWith (\name argument -> (name, F.FApp (F.FTC tycon) argument)) names [F.FInt, F.boolSort]
    enums = instances enumTycon ["enumInt", "enumBool"]
    payloads = instances payloadTycon ["payloadInt", "payloadBool"]
    enumFirst = [F.EEq (F.EVar name) (F.ECst (F.EVar "PhantomFirst") sort) | (name, sort) <- enums]
    enumCoverage =
        [ F.POr [F.EEq (F.EVar name) (F.ECst (F.EVar constructor) sort) | constructor <- ["PhantomFirst", "PhantomSecond"]]
        | (name, sort) <- enums
        ]
    payloadValue name = F.EApp (F.EVar "phantomValue") (F.EVar name)
    payloadCoverage =
        [ F.EEq (F.EVar name) (F.EApp (F.ECst (F.EVar "PhantomValue") (F.FFunc F.FInt sort)) (payloadValue name))
        | (name, sort) <- payloads
        ]
    payloadZero = [F.EEq (payloadValue name) (F.expr (0 :: Integer)) | (name, _) <- payloads]
    query solver expression expected =
        withSMT (SMT.makeContextWithSEnv cfg "phantom datatype" environment mempty) $ do
            SMT.smtAssert (So.elaborate parameter expression)
            actual <- SMT.command SMT.CheckSat
            liftIO (actual @?= expected)
      where
        cfg = C.defConfig{C.solver = solver, C.smtTimeout = Just 2000}
        theory = Theory.theorySymbols declarations <> So.theoryEnv cfg (mempty :: F.SInfo ())
        names = F.fromListSEnv (enums ++ payloads) <> fmap F.tsSort theory
        environment = F.symEnv cfg names theory declarations mempty []
        parameter = So.ElabParam (C.solverFlags cfg) "phantom datatype" environment

-- Direct and annotated operations require both a proof and an actual model.
-- Escaping callables use quantified equations: their satisfiable companions
-- can be incomplete, but an unknown response is never accepted as a proof.
collectionTests :: TestTree
collectionTests =
    testGroup
        "selected collection interpretations"
        [ testGroup
            "operations"
            [ testCase (show (solver, form, name, valid)) $
                collectionQuery
                    solver
                    (law form name signature arguments observe expected valid)
                    (if valid then SMT.Unsat else SMT.Sat)
            | solver <- [C.Z3, C.Cvc5]
            , form <- [Bare, Annotated]
            , (name, signature, arguments, observe, expected) <- cases
            , valid <- [True, False]
            ]
        , testGroup
            "native values (unknown is not a proof)"
            [ testCase (show (solver, form, name, valid))
                $ collectionCheckWith
                    id
                    solver
                    (law form name signature arguments observe expected valid)
                $ \actual ->
                    if valid
                        then actual @?= SMT.Unsat
                        else assertBool ("false law was proved: " ++ show actual) (actual == SMT.Sat || actual == SMT.Unknown)
            | solver <- [C.Z3, C.Cvc5]
            , form <- [WholeValue, PartialValue]
            , (name, signature, arguments, observe, expected) <- cases
            , name `elem` [Theory.setSub, Theory.bagSub, Theory.mapSel]
            , valid <- [True, False]
            ]
        , testGroup
            "lexical native-name owners"
            [ testCase (show (solver, name, valid)) $
                collectionQuery
                    solver
                    ( F.ELet
                        name
                        (F.ECst (F.EVar "local") (F.FFunc F.FInt F.FInt))
                        ( F.PAnd
                            [ F.EEq (F.EApp (F.EVar name) zero) one
                            , (if valid then F.PNot else id) (F.EEq (F.EApp (F.EVar name) zero) one)
                            ]
                        )
                    )
                    (if valid then SMT.Unsat else SMT.Sat)
            | solver <- [C.Z3, C.Cvc5]
            , name <- [Theory.setSub, Theory.bagSng, Theory.mapDef]
            , valid <- [True, False]
            ]
        , testCase "incompatible native occurrence casts remain rejected" $
            let cfg = C.defConfig
                environment = collectionEnvironment cfg
                parameter = So.ElabParam (C.solverFlags cfg) "malformed collection annotation" environment
             in assertBool "malformed Set_sub annotation was erased" $
                    either (const True) (const False) $
                        So.elabExprE
                            parameter
                            Nothing
                            (F.eApps (F.ECst (F.EVar Theory.setSub) (F.FFunc F.FInt (F.FFunc F.FInt F.boolSort))) [zero, zero])
        , testGroup
            "array-valued elements do not choose the container representation"
            [ testCase (show (solver, valid)) $
                let element = F.ECst (app Theory.mapDef [one]) mt
                    container = app Theory.setSng [element]
                    observed = app Theory.setMem [element, container]
                 in collectionQuery
                        solver
                        ((if valid then F.PNot else id) observed)
                        (if valid then SMT.Unsat else SMT.Sat)
            | solver <- [C.Z3, C.Cvc5]
            , valid <- [True, False]
            ]
        , testGroup
            "the declaration owns a global native meaning"
            [ testCase (show (solver, name, valid)) $
                let extend environment =
                        environment
                            { F.seTheory = F.insertSEnv name (F.Thy name raw signature F.Theory) (F.seTheory environment)
                            , F.seSort = F.insertSEnv name signature (F.seSort environment)
                            }
                    actual = observe (app name arguments)
                    predicate = F.EEq actual expected
                 in collectionQueryWith
                        extend
                        solver
                        ((if valid then F.PNot else id) predicate)
                        (if valid then SMT.Unsat else SMT.Sat)
            | solver <- [C.Z3, C.Cvc5]
            , (name, raw, signature, arguments, observe, expected) <-
                [ (Theory.setSub, "=", fun [st, st] F.boolSort, [emptySet, singleton], id, F.PFalse)
                , ("subsetAlias", "set.subset", fun [st, st] F.boolSort, [emptySet, singleton], id, F.PTrue)
                , (Theory.setEmpty, "not", fun [F.boolSort] F.boolSort, [F.PTrue], id, F.PFalse)
                , ("constantAlias", "const", fun [F.FInt] (F.arraySort F.boolSort F.FInt), [one], \array -> app Theory.arrSelectM [array, F.PTrue], one)
                ]
            , valid <- [True, False]
            ]
        ]
  where
    zero = F.expr (0 :: Integer)
    one = F.expr (1 :: Integer)
    two = F.expr (2 :: Integer)
    three = F.expr (3 :: Integer)
    st = F.setSort F.FInt
    bt = F.bagSort F.FInt
    mt = F.mapSort F.FInt F.FInt
    fun args result = foldr F.FFunc result args
    app name = F.eApps (F.EVar name)
    emptySet = F.ECst (app Theory.setEmpty [zero]) st
    singleton = app Theory.setSng [zero]
    member value = app Theory.setMem [zero, value]
    bag multiplicity = app Theory.bagSng [zero, multiplicity]
    count value = app Theory.bagCount [zero, value]
    mapping = F.ECst (app Theory.mapDef [one]) mt
    selected value = app Theory.mapSel [value, zero]
    cases =
        [ (Theory.setEmpty, fun [F.FInt] st, [zero], member, F.PFalse)
        , (Theory.setEmp, fun [st] F.boolSort, [emptySet], id, F.PTrue)
        , (Theory.setSng, fun [F.FInt] st, [zero], member, F.PTrue)
        , (Theory.setAdd, fun [F.FInt, st] st, [zero, emptySet], member, F.PTrue)
        , (Theory.setMem, fun [F.FInt, st] F.boolSort, [zero, singleton], id, F.PTrue)
        , (Theory.setCup, fun [st, st] st, [singleton, emptySet], member, F.PTrue)
        , (Theory.setCap, fun [st, st] st, [singleton, emptySet], member, F.PFalse)
        , (Theory.setDif, fun [st, st] st, [singleton, singleton], member, F.PFalse)
        , (Theory.setSub, fun [st, st] F.boolSort, [singleton, emptySet], id, F.PFalse)
        , (Theory.setCom, fun [st] st, [singleton], member, F.PFalse)
        , (Theory.bagEmpty, fun [F.FInt] bt, [zero], count, zero)
        , (Theory.bagSng, fun [F.FInt, F.FInt] bt, [zero, two], count, two)
        , (Theory.bagCount, fun [F.FInt, bt] F.FInt, [zero, bag two], id, two)
        , (Theory.bagCup, fun [bt, bt] bt, [bag one, bag two], count, three)
        , (Theory.bagSub, fun [bt, bt] F.boolSort, [bag two, bag one], id, F.PFalse)
        , (Theory.bagMax, fun [bt, bt] bt, [bag one, bag two], count, two)
        , (Theory.bagMin, fun [bt, bt] bt, [bag one, bag two], count, one)
        , (Theory.mapDef, fun [F.FInt] mt, [one], selected, one)
        , (Theory.mapSel, fun [mt, F.FInt] F.FInt, [mapping, zero], id, one)
        , (Theory.mapSto, fun [mt, F.FInt, F.FInt] mt, [mapping, zero, two], selected, two)
        ]
    law form name signature arguments observe expected valid =
        case (form, arguments, signature) of
            (Bare, _, _) -> result (app name arguments)
            (Annotated, _, _) -> result (F.eApps native arguments)
            (WholeValue, _, _) -> alias signature native arguments
            (PartialValue, first : rest, F.FFunc _ remaining) -> alias remaining (F.EApp native first) rest
            _ -> error "collection operation must have an argument"
      where
        native = F.ECst (F.EVar name) signature
        result expression = (if valid then F.PNot else id) (F.EEq (observe expression) expected)
        alias sort value args =
            F.PExist [("collectionFunction", sort)] $
                F.PAnd [F.EEq (F.EVar "collectionFunction") value, result (app "collectionFunction" args)]

data CollectionForm = Bare | Annotated | WholeValue | PartialValue deriving (Show)

cardinalityTests :: TestTree
cardinalityTests =
    testGroup
        "backend cardinality ownership"
        [ testCase (show solver ++ " " ++ label) $
            collectionQueryWith extend solver predicate expected
        | solver <- [C.Z3, C.Cvc5]
        , let uninterpreted = if solver == C.Z3 then SMT.Sat else SMT.Unsat
        , (label, predicate, expected) <-
            [ ("nominal instance preserves congruence", F.PAnd [F.EEq nominalCard zero, F.PAtom F.Ne nominalCard zero], SMT.Unsat)
            , ("distinct carriers have well-sorted instances", F.PAnd [F.EEq nominalCard zero, F.EEq (card F.FInt) one], uninterpreted)
            , ("native empty cardinality is not invented for the fallback", F.PAtom F.Ne nominalCard zero, uninterpreted)
            , ("first-class cardinality agrees with its direct call", firstClass, SMT.Unsat)
            , ("lexical cardinality name remains local", shadow, SMT.Unsat)
            ]
        ]
  where
    zero = F.ECon (F.I 0)
    one = F.ECon (F.I 1)
    app name = F.eApps (F.EVar name)
    constructor = F.symbolFTycon (F.dummyLoc "CardinalityElement")
    declaration = F.DDecl constructor 0 [F.DCtor (F.dummyLoc "CardinalityElement") []]
    nominal = F.FTC constructor
    empty sort = F.ECst (app Theory.setEmpty [zero]) (F.setSort sort)
    card sort = app Theory.setCard [empty sort]
    nominalCard = card nominal
    signature = F.FFunc (F.setSort nominal) F.FInt
    firstClass =
        F.PExist [("observedCard", signature)] $
            F.PAnd
                [ F.EEq (F.EVar "observedCard") (F.ECst (F.EVar Theory.setCard) signature)
                , F.PAtom F.Ne (app "observedCard" [empty nominal]) nominalCard
                ]
    shadow = F.ELet Theory.setCard (F.ELam ("n", F.FInt) (F.EVar "n")) (F.PAtom F.Ne (app Theory.setCard [zero]) zero)
    extend environment =
        environment
            { F.seSort = (F.tsSort <$> native) <> F.seSort environment
            , F.seTheory = native <> F.seTheory environment
            , F.seData = F.insertSEnv (F.symbol declaration) declaration (F.seData environment)
            }
    native = Theory.theorySymbols [declaration]

collectionEnvironment :: C.Config -> F.SymEnv
collectionEnvironment cfg = F.symEnv cfg names theory [] mempty []
  where
    theory = So.theoryEnv cfg (mempty :: F.SInfo ())
    names = F.insertSEnv "local" (F.FFunc F.FInt F.FInt) (F.tsSort <$> theory)

collectionQuery :: C.SMTSolver -> F.Expr -> SMT.Response -> Assertion
collectionQuery = collectionQueryWith id

collectionQueryWith :: (F.SymEnv -> F.SymEnv) -> C.SMTSolver -> F.Expr -> SMT.Response -> Assertion
collectionQueryWith extend solver expression expected =
    collectionCheckWith extend solver expression (@?= expected)

collectionCheckWith :: (F.SymEnv -> F.SymEnv) -> C.SMTSolver -> F.Expr -> (SMT.Response -> Assertion) -> Assertion
collectionCheckWith extend solver expression oracle =
    withSMT (SMT.makeContextWithSEnv cfg "collection interpretation" environment mempty) $ do
        if solver == C.Z3 then SMT.smtSetMbqi else pure ()
        SMT.smtAssert (So.elaborate parameter expression)
        actual <- SMT.command SMT.CheckSat
        liftIO (oracle actual)
  where
    cfg = C.defConfig{C.solver = solver, C.allowHO = True, C.smtTimeout = Just 2000}
    environment = extend (collectionEnvironment cfg)
    parameter = So.ElabParam (C.solverFlags cfg) "collection interpretation" environment

-- A source value such as @opaque :: forall a. Box a@ has no supplied equation.
-- Its occurrences share identity at one selected sort, not across native sorts.
-- Function instances also remain distinct even though both use the Int carrier.
opaqueConstantTests :: TestTree
opaqueConstantTests =
    testGroup
        "opaque polymorphic constants"
        [ testGroup
            (show solver)
            [ testCase label $ query solver nested expression expected
            | (label, nested, expression, expected) <- cases
            ]
        | solver <- [C.Z3, C.Cvc5]
        ]
  where
    tycon = F.symbolFTycon (F.dummyLoc "OpaqueBox")
    box = F.FApp (F.FTC tycon)
    declaration =
        F.DDecl
            tycon
            1
            [ F.DCtor (F.dummyLoc "OpaqueEmpty") []
            , F.DCtor (F.dummyLoc "OpaqueFull") [F.DField (F.dummyLoc "opaqueField") (F.FVar 0)]
            ]
    at name sort = F.ECst (F.EVar name) (box sort)
    functionAt name sort = F.ECst (F.EVar name) (F.FFunc (box sort) F.boolSort)
    sameInt = F.EEq (functionAt "f" F.FInt) (functionAt "g" F.FInt)
    stringList = F.FApp (F.FTC F.listFTyCon) F.charSort
    pair name =
        F.PAnd
            [ F.EEq (F.EVar "i") (at name F.FInt)
            , F.EEq (F.EVar "b") (at name F.boolSort)
            ]
    contradiction name = F.PAnd [pair name, F.PAtom F.Ne (F.EVar "b") (at name F.boolSort)]
    full = F.EApp (F.EVar "OpaqueFull") F.PTrue
    distinctInstances =
        F.PAnd
            [ F.EEq (at "opaque" F.FInt) (at "OpaqueEmpty" F.FInt)
            , F.EEq (at "opaque" F.boolSort) full
            ]
    shadow =
        F.PAnd
            [ F.EEq (at "opaque" F.boolSort) (at "OpaqueEmpty" F.boolSort)
            , F.PExist [("opaque", box F.boolSort)] (F.EEq (F.EVar "opaque") full)
            ]
    cases =
        [ ("same selected instance cannot contradict itself", False, contradiction "opaque", SMT.Unsat)
        , ("different selected instances have independent values", False, distinctInstances, SMT.Sat)
        , ("monomorphic global retains its declared carrier", False, F.EEq (F.EVar "b") (F.EVar "mono"), SMT.Sat)
        , ("native nullary constructor supports both instances", False, pair "OpaqueEmpty", SMT.Sat)
        , ("native constructor identity remains consistent", False, contradiction "OpaqueEmpty", SMT.Unsat)
        , ("instance declarations are recreated after pop", True, distinctInstances, SMT.Sat)
        , ("lexical shadow is independent of the global instance", False, shadow, SMT.Sat)
        , ("function equality at Int does not equate Bool instances", False, F.PAnd [sameInt, F.PAtom F.Ne (functionAt "f" F.boolSort) (functionAt "g" F.boolSort)], SMT.Sat)
        , ("function instances can differ at an observed Bool argument", False, F.PAnd [sameInt, F.EApp (functionAt "f" F.boolSort) (F.EVar "b"), F.PNot (F.EApp (functionAt "g" F.boolSort) (F.EVar "b"))], SMT.Sat)
        , ("source string aliases select the same value instance", False, F.PAtom F.Ne (at "opaque" F.strSort) (at "opaque" stringList), SMT.Unsat)
        , ("source aliases inside function sorts select the same instance", False, F.PAtom F.Ne (functionAt "f" F.strSort) (functionAt "f" stringList), SMT.Unsat)
        ]
    query solver nested expression expected =
        withSMT (SMT.makeContextWithSEnv cfg "opaque-constant" environment mempty) $ do
            let action = SMT.smtAssert elaborated >> SMT.command SMT.CheckSat
            responses <-
                if nested
                    then sequence [SMT.smtBracket "first opaque scope" action, SMT.smtBracket "second opaque scope" action]
                    else sequence [action]
            liftIO (mapM_ (@?= expected) responses)
      where
        cfg = C.defConfig{C.solver = solver, C.allowHO = True, C.smtTimeout = Just 2000}
        theory = Theory.theorySymbols [declaration] <> So.theoryEnv cfg (mempty :: F.SInfo ())
        names =
            F.fromListSEnv
                [ ("opaque", F.FAbs 0 (box (F.FVar 0)))
                , ("mono", box F.boolSort)
                , ("i", box F.FInt)
                , ("b", box F.boolSort)
                , ("f", F.FAbs 0 (F.FFunc (box (F.FVar 0)) F.boolSort))
                , ("g", F.FAbs 0 (F.FFunc (box (F.FVar 0)) F.boolSort))
                ]
                <> fmap F.tsSort theory
        environment = F.symEnv cfg names theory [declaration] mempty []
        elaborated = So.elaborate (So.ElabParam (C.solverFlags cfg) "opaque constant instance" environment) expression

polymorphicOccurrenceTests :: TestTree
polymorphicOccurrenceTests =
    testGroup
        "selected polymorphic constructor occurrences"
        [ testCase "a bare native value retains its opened occurrence sort" $
            case So.elabExpr parameter Nothing (F.EVar "Method") of
                F.ECst (F.EVar "Method") (F.FFunc (F.FFunc argument result) (F.FApp _ parameterSort)) -> do
                    argument @?= parameterSort
                    result @?= F.boolSort
                    assertBool "declaration forall coordinate escaped unchanged" (argument /= F.FVar 0)
                other -> assertFailure (show other)
        , testCase "unequal-carrier relations retain both selected native occurrences" $
            mapM_
                ( \relation -> case So.elabExpr parameter Nothing (F.PAtom relation (F.EVar "Method") (F.EVar "Method")) of
                    F.PAtom _ (F.ECst (F.EVar "Method") F.FFunc{}) (F.ECst (F.EVar "Method") F.FFunc{}) -> pure ()
                    other -> assertFailure (show other)
                )
                [F.Ueq, F.Une]
        , testCase "a native equality with an opened occurrence has an actual model" $
            query (F.PAtom F.Ueq (F.EVar "Method") (F.ECst (F.EVar "Method") (constructorSort F.FInt))) SMT.Sat
        , testCase "later result equations close the selected occurrence annotation" $ do
            let expression = F.ELet "selected" (F.EVar "Method") (F.EApp (F.EVar "selected") (F.EVar "intCallback"))
            case So.elabExpr parameter (Just (methodSort F.FInt)) expression of
                F.ELet _ (F.ECst (F.EVar "Method") selected) _ -> selected @?= constructorSort F.FInt
                other -> assertFailure (show other)
        , testCase "one judgment keeps independent Int and Bool native instances" $ do
            let entries = M.keys (F.seInstancesCur (execState (SMT.smt2 (So.elaborate parameter aliases)) environment))
            length entries @?= 2
            assertBool "missing integer instance" (("Method", constructorSort F.FInt) `elem` entries)
            assertBool "missing Boolean instance" (("Method", constructorSort F.boolSort) `elem` entries)
        , testCase "nominal string-like native instances retain source identity" $ do
            let entries = selectedEntries nominalA nominalB
            length entries @?= 2
            assertBool "missing first nominal instance" (("Method", constructorSort nominalA) `elem` entries)
            assertBool "missing second nominal instance" (("Method", constructorSort nominalB) `elem` entries)
        , testCase "canonical String and Char-list native instances share source identity" $
            selectedEntries F.strSort (F.FApp (F.FTC F.listFTyCon) F.charSort) @?= [("Method", constructorSort F.strSort)]
        , testCase "first-class nominal string instances preserve their actual callbacks" $
            queryWith nominalEnvironment (F.PAnd [nominalAliases, F.PNot (F.PAnd [same "nominalBuilderA" "nominalCallbackA", same "nominalBuilderB" "nominalCallbackB"])]) SMT.Unsat
        , testCase "nominal string instances retain a false-callback countermodel" $
            queryWith nominalEnvironment (F.PAnd [nominalAliases, F.PAtom F.Ne (F.EVar "nominalCallbackA") (F.EVar "otherNominalCallbackA"), F.PAtom F.Ne (F.EApp (F.EVar "nominalBuilderA") (F.EVar "nominalCallbackA")) (native "otherNominalCallbackA")]) SMT.Sat
        , testCase "fully applied constructor selection retains its callback" $
            query (F.PNot (F.PAtom F.Eq (F.EApp (F.EVar "method") (native "intCallback")) (F.EVar "intCallback"))) SMT.Unsat
        , testCase "first-class Int and Bool constructor meanings are both retained" $
            query (F.PAnd [aliases, F.PNot (F.PAnd [same "intBuilder" "intCallback", same "boolBuilder" "boolCallback"])]) SMT.Unsat
        , testCase "independent Int and Bool constructor instances are jointly inhabited" $
            query aliases SMT.Sat
        , testCase "first-class constructor does not replace its actual callback" $
            query (F.PAnd [aliases, F.PAtom F.Ne (F.EVar "intCallback") (F.EVar "otherIntCallback"), F.PAtom F.Eq (F.EApp (F.EVar "intBuilder") (F.EVar "intCallback")) (native "otherIntCallback")]) SMT.Unsat
        , testCase "different callbacks retain a real first-class constructor countermodel" $
            query (F.PAnd [aliases, F.PAtom F.Ne (F.EVar "intCallback") (F.EVar "otherIntCallback"), F.PAtom F.Ne (F.EApp (F.EVar "intBuilder") (F.EVar "intCallback")) (native "otherIntCallback")]) SMT.Sat
        , testCase "a lexical native-name shadow remains an arbitrary callable" $
            query (F.PNot (F.PAll [("Method", constructorSort F.FInt)] (F.PAtom F.Eq (F.EApp (F.EVar "Method") (F.EVar "intCallback")) (F.EApp (F.EVar "Method") (F.EVar "otherIntCallback"))))) SMT.Sat
        , testCase "an incompatible constructor argument remains rejected" $
            assertBool "native constructor accepted a non-callable field" (either (const True) (const False) (So.elabExprE parameter Nothing (F.EApp (F.EVar "Method") F.PTrue)))
        ]
  where
    cfg = C.defConfig{C.solver = C.Z3, C.allowHO = True, C.smtTimeout = Just 2000}
    tycon = F.symbolFTycon (F.dummyLoc "Method")
    declaration = F.DDecl tycon 1 [F.DCtor (F.dummyLoc "Method") [F.DField (F.dummyLoc "method") (F.FFunc (F.FVar 0) F.boolSort)]]
    methodSort argument = F.FApp (F.FTC tycon) argument
    constructorSort argument = F.FFunc (F.FFunc argument F.boolSort) (methodSort argument)
    nominal name = F.FTC (F.mappendFTC (F.symbolFTycon (F.dummyLoc name)) F.strFTyCon)
    nominalA = nominal "TextLikeA"
    nominalB = nominal "TextLikeB"
    theory = Theory.theorySymbols [declaration] <> So.theoryEnv cfg (mempty :: F.SInfo ())
    names = F.fromListSEnv [("intCallback", F.FFunc F.FInt F.boolSort), ("otherIntCallback", F.FFunc F.FInt F.boolSort), ("boolCallback", F.FFunc F.boolSort F.boolSort), ("intBuilder", constructorSort F.FInt), ("boolBuilder", constructorSort F.boolSort)] <> fmap F.tsSort theory
    environment = F.symEnv cfg names theory [declaration] mempty []
    parameter = So.ElabParam (C.solverFlags cfg) "native constructor occurrence" environment
    selectedEntries first second =
        M.keys (F.seInstancesCur (execState (SMT.smt2 (So.elaborate parameter expression)) environment))
      where
        at argument = F.ECst (F.EVar "Method") (constructorSort argument)
        expression :: F.Expr
        expression = F.PAnd [F.EEq (at argument) (at argument) | argument <- [first, second]]
    nominalEnvironment =
        F.insertsSymEnv
            environment
            [("nominalBuilderA", constructorSort nominalA), ("nominalBuilderB", constructorSort nominalB), ("nominalCallbackA", F.FFunc nominalA F.boolSort), ("otherNominalCallbackA", F.FFunc nominalA F.boolSort), ("nominalCallbackB", F.FFunc nominalB F.boolSort)]
    nominalAliases = F.PAnd [F.EEq (F.EVar name) (F.EVar "Method") | name <- ["nominalBuilderA", "nominalBuilderB"]]
    aliases :: F.Expr
    aliases = F.PAnd [F.PAtom F.Eq (F.EVar name) (F.EVar "Method") | name <- ["intBuilder", "boolBuilder"]]
    native name = F.EApp (F.EVar "Method") (F.EVar name)
    same builder callback = F.PAtom F.Eq (F.EApp (F.EVar builder) (F.EVar callback)) (native callback)
    query = queryWith environment
    queryWith env expression expected =
        withSMT (SMT.makeContextWithSEnv cfg "native-occurrence" env mempty) $ do
            SMT.smtSetMbqi
            SMT.smtAssert (So.elaborate (So.ElabParam (C.solverFlags cfg) "native constructor occurrence" env) expression)
            actual <- SMT.command SMT.CheckSat
            liftIO (actual @?= expected)

booleanGood, booleanBad, arrayGood, arrayBad :: F.Expr
booleanGood = F.PAnd [booleanAlias, F.EApp (F.EVar "callback") F.PTrue]
booleanBad = F.PAnd [booleanAlias, F.PNot (F.EApp (F.EVar "callback") F.PTrue)]
booleanAlias :: F.Expr
booleanAlias = F.EEq (F.EVar "callback") (F.EVar "nativeNot")

arrayGood = F.PAnd [arrayAlias, F.PNot arrayCall]
arrayBad = F.PAnd [arrayAlias, arrayCall]
arrayAlias, arrayCall :: F.Expr
arrayAlias = F.EEq (F.EVar "selectCallback") (F.EVar "arr_select_m")
arrayCall =
    F.eApps
        (F.EVar "selectCallback")
        [F.ECst (F.EApp (F.EVar "arr_const_m") F.PTrue) (F.arraySort F.boolSort F.boolSort), F.PFalse]

indexedGood :: F.Expr
indexedGood =
    F.PAtom
        F.Ne
        ( F.ECst
            ( F.eApps
                (F.EVar "app")
                [ F.eApps (F.EVar "_") [F.EVar "zero_extend", F.expr (2 :: Integer)]
                , F.ECon (F.L "#b1000" (F.sizedBitVecSort "Size4"))
                ]
            )
            (F.sizedBitVecSort "Size6")
        )
        (F.ECon (F.L "#b001000" (F.sizedBitVecSort "Size6")))

applicationGood :: F.Expr
applicationGood =
    F.PAnd
        [ booleanAlias
        , F.EEq (F.EVar "application") (F.EVar "app")
        , F.eApps (F.EVar "application") [F.EVar "callback", F.PTrue]
        ]

check :: C.SMTSolver -> Bool -> (SMT.Response -> Assertion) -> F.Expr -> Assertion
check solver nested oracle expression =
    withSMT (SMT.makeContextWithSEnv cfg "native-callable" environment mempty) $ do
        if solver == C.Z3 then SMT.smtSetMbqi else pure ()
        let action = SMT.smtAssert elaborated >> SMT.command SMT.CheckSat
        responses <-
            if nested
                then sequence [SMT.smtBracket "first native scope" action, SMT.smtBracket "second native scope" action]
                else sequence [action]
        liftIO (mapM_ oracle responses)
  where
    cfg = C.defConfig{C.solver = solver, C.allowHO = True, C.smtTimeout = Just 2000}
    native = F.Thy "nativeNot" "not" (F.FFunc F.boolSort F.boolSort) F.Theory
    theory = F.insertSEnv "nativeNot" native (So.theoryEnv cfg (mempty :: F.SInfo ()))
    names =
        F.fromListSEnv
            [ ("callback", F.FFunc F.boolSort F.boolSort)
            , ("application", F.FFunc (F.FFunc F.boolSort F.boolSort) (F.FFunc F.boolSort F.boolSort))
            , ("selectCallback", F.FFunc (F.arraySort F.boolSort F.boolSort) (F.FFunc F.boolSort F.boolSort))
            ]
            <> (F.tsSort <$> theory)
    literals = F.fromListSEnv [(F.symbol value, F.strSort) | value <- V.symConsts expression]
    environment = F.symEnv cfg (names <> literals) theory [] literals []
    elaborated = So.elaborate (So.ElabParam (C.solverFlags cfg) "native callable" environment) expression

withSMT :: IO SMT.Context -> StateT SMT.Context IO a -> IO a
withSMT acquire action = bracket acquire SMT.cleanupContext (evalStateT action)
