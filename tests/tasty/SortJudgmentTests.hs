{-# LANGUAGE OverloadedStrings #-}

module SortJudgmentTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (runReader)
import Control.Monad.State (StateT, evalStateT, gets)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (isInfixOf)
import Data.Maybe (isJust, isNothing)
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Theories as Theory
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import qualified NativeCarrierInferenceTests
import qualified PreparedElaborationTests
import SortInventoryTests (allocationBytes)
import SourceCheckScopeTests (jointSorts, preparedCheckingTests, qualifierTests)
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase, (@?=))

tests :: TestTree
tests = testGroup "sort judgments" [unificationTests, nativeTests, carrierTests, reflexiveTests, seedTests, singleTests, qualifierTests, numericTests, binderNormalizationTests, numericOwnershipTests, checkableNormalizationTests, binderElaborationTests, preparedCheckingTests, PreparedElaborationTests.tests, NativeCarrierInferenceTests.tests]

binderElaborationTests :: TestTree
binderElaborationTests =
    testGroup
        "public binder elaboration"
        [ testGroup
            "matching body casts"
            [ testCase (binderName ++ "/" ++ sortName ++ "/arrays=" ++ show arrays) $ do
                let flags = Config.ElabFlags arrays False
                    body :: F.Expr
                    body = F.PAtom F.Eq (F.ECst (F.EVar "x") source) (F.EVar "x")
                    result :: F.Expr
                    result = C.elaborate (C.ElabParam flags "binder sort" F.emptySymEnv) (bind source body)
                assertBool "matching source cast rejected" (isJust (C.checkSortExpr Nothing F.dummySpan mempty result))
            | (binderName, bind) <- binders
            , (sortName, source) <- sorts
            , arrays <- [False, True]
            ]
        , testGroup
            "incompatible body casts"
            [ testCase (binderName ++ "/" ++ castName ++ "/arrays=" ++ show arrays) $ do
                let flags = Config.ElabFlags arrays False
                    body :: F.Expr
                    body = F.PAtom F.Eq (F.ECst (F.EVar "x") target) (F.EVar "x")
                    result :: F.Expr
                    result = C.elaborate (C.ElabParam flags "binder cast" F.emptySymEnv) (bind source body)
                outcome <- try (evaluate (length (show result))) :: IO (Either SomeException Int)
                case outcome of
                    Left failure -> assertBool (show failure) ("incompatible sort" `isInfixOf` show failure)
                    Right _ -> assertFailure "incompatible cast admitted"
            | (binderName, bind) <- binders
            , (castName, source, target) <- mismatches
            , arrays <- [False, True]
            ]
        ]
  where
    binders =
        [ ("lambda", \source -> F.ELam ("x", source))
        , ("forall", \source -> F.PAll [("x", source)])
        , ("exists", \source -> F.PExist [("x", source)])
        ]
    sorts =
        [ ("set", F.setSort F.intSort)
        , ("bag", F.bagSort F.intSort)
        , ("array", F.arraySort F.intSort F.boolSort)
        , ("map", F.mapSort F.intSort F.intSort)
        ]
    mismatches =
        [ ("wrong array range", F.arraySort F.intSort F.boolSort, F.arraySort F.intSort F.intSort)
        , ("wrong array element", F.arraySort F.intSort F.boolSort, F.arraySort F.boolSort F.boolSort)
        , ("array to int", F.arraySort F.intSort F.boolSort, F.intSort)
        ]

checkableNormalizationTests :: TestTree
checkableNormalizationTests =
    testGroup
        "source validation sort normalization"
        [ testGroup
            (label ++ if lowerSets then " array-backed" else " native sets")
            [ testCase "checkSorted accepts a source-typed lambda argument" $
                accepted (runReader (C.checkSorted Nothing F.dummySpan environment application) flags)
            , testCase "checkSortFull accepts the same lambda argument" $
                accepted (runReader (C.checkSortFull Nothing F.dummySpan refinements F.boolSort application) flags)
            , testCase "checkSortedReftFull uses the same source interpretation" $
                accepted (runReader (C.checkSortedReftFull Nothing F.dummySpan refinements (F.RR F.boolSort (F.Reft ("result", application)))) flags)
            , testCase "result ascription and expected sort normalize together" $
                accepted (runReader (C.checkSortFull Nothing F.dummySpan refinements source (F.ECst value source)) flags)
            , testCase "quantifier binders and declared values normalize together" $
                accepted (runReader (C.checkSortFull Nothing F.dummySpan refinements F.boolSort (F.PAll [("local", source)] (F.PAtom F.Eq local value))) flags)
            , testCase "normalization does not widen container elements" $
                assertBool "mismatched container argument admitted" $
                    isJust (runReader (C.checkSortFull Nothing F.dummySpan refinements F.boolSort (applied mismatch)) flags)
            , testCase "normalization does not replace an argument's declared carrier" $
                assertBool "mismatched container cast admitted" $
                    isJust (runReader (C.checkSortFull Nothing F.dummySpan refinements mismatch (F.ECst value mismatch)) flags)
            ]
        | (label, source, mismatch) <-
            [ ("set", F.setSort F.FInt, F.setSort F.FReal)
            , ("map with nested set", F.mapSort F.FInt (F.setSort F.FInt), F.mapSort F.FInt (F.setSort F.FReal))
            ]
        , lowerSets <- [False, True]
        , let flags = Config.ElabFlags lowerSets False
              environment = F.fromListSEnv [("value", source)]
              refinements = F.trueSortedReft <$> environment
              application = applied source
        ]
  where
    value, local :: F.Expr
    value = F.EVar "value"
    local = F.EVar "local"
    applied :: F.Sort -> F.Expr
    applied source = F.EApp (F.ELam ("local", source) (F.PAtom F.Eq local local)) value
    accepted = maybe (pure ()) (assertFailure . show)

numericOwnershipTests :: TestTree
numericOwnershipTests =
    testGroup
        "numeric declaration ownership"
        [ testCase "standalone validity consumes the elaborated numeric judgment" $
            withSystemTempDirectory "numeric-validity" $ \directory -> do
                let half = F.EBin F.Div (numericReal 1) (numericReal 2)
                    correct = F.PAtom F.Eq half (numericReal 0.5)
                    incorrect = F.PAtom F.Eq half (numericReal 0)
                    config = Config.defConfig{Config.solver = Config.Z3}
                SMT.checkValid config (directory ++ "/correct") [] F.PTrue correct >>= (@?= True)
                SMT.checkValid config (directory ++ "/incorrect") [] F.PTrue incorrect >>= (@?= False)
                SMT.checkValids config (directory ++ "/batch") [] [correct, incorrect] >>= (@?= [True, False])
        , testCase "typed native application spines retain read-after-write and countermodels" $
            withSystemTempDirectory "numeric-native-spine" $ \directory -> do
                let config = Config.defConfig{Config.solver = Config.Z3}
                    declarations = [("array", F.arraySort F.FInt F.FInt)]
                    index = numericInt 7
                    selected store select = F.eApps (F.EVar select) [F.eApps (F.EVar store) [F.EVar "array", index, numericInt 42], index]
                mapM_
                    ( \(store, select) ->
                        SMT.checkValids config (directory ++ "/native") declarations [F.PAtom F.Eq (selected store select) (numericInt n) | n <- [42, 43]]
                            >>= (@?= [True, False])
                    )
                    [(Theory.arrStoreM, Theory.arrSelectM), ("store", "select")]
        , testCase "typed ordinary application spines do not acquire native meaning" $
            withSystemTempDirectory "numeric-ordinary-spine" $ \directory -> do
                let config = Config.defConfig{Config.solver = Config.Z3}
                    declarations = [("select", F.FFunc F.FInt (F.FFunc F.FInt F.FInt))]
                    application n = F.eApps (F.EVar "select") [numericInt 7, numericInt n]
                SMT.checkValids config (directory ++ "/ordinary") declarations [F.PAtom F.Eq (application 42) (application n) | n <- [42, 43]]
                    >>= (@?= [True, False])
        , testCase "a free fractional declaration is not rebound by an inner kind" $ do
            let expression = F.PAll [("alpha", F.FNum)] (F.PAtom F.Eq (F.EBin F.Div (F.EVar "x") (numericInt 2)) (numericReal 0.5))
            actual <- numericScopeQuery fractionalEnvironment [("x", fractionalSort)] [F.PAtom F.Eq (F.EVar "x") (numericReal 1)] (F.PNot expression)
            actual @?= SMT.Unsat
        , testCase "a free fractional declaration still admits a countermodel" $ do
            let expression = F.PAll [("alpha", F.FNum)] (F.PAtom F.Eq (F.EBin F.Div (F.EVar "x") (numericInt 2)) (numericReal 0))
            actual <- numericScopeQuery fractionalEnvironment [("x", fractionalSort)] [F.PAtom F.Eq (F.EVar "x") (numericReal 1)] (F.PNot expression)
            actual @?= SMT.Sat
        , testCase "a free numeric declaration remains integer under a fractional kind" $ do
            let environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("alpha", F.FNum), ("x", fractionalSort)]}
                expression = F.PAll [("alpha", F.FFrac)] (F.PAtom F.Eq (F.EBin F.Div (F.EVar "x") (numericInt 2)) (numericInt 0))
            numericScopeQuery environment [("x", fractionalSort)] [F.PAtom F.Eq (F.EVar "x") (numericInt 1)] (F.PNot expression) >>= (@?= SMT.Unsat)
        , testCase "an unrelated local kind cannot make a nominal global fractional" $ do
            let expression = F.PAll [("alpha", F.FFrac)] (F.PAtom F.Eq (F.ECst (F.EVar "x") F.FReal) (numericReal 0))
                identity = F.PAll [("alpha", F.FFrac)] (F.PAtom F.Eq (F.EVar "x") (F.EVar "x"))
            mapM_
                ( \environment -> do
                    C.checkSortExpr Nothing F.dummySpan environment expression @?= Nothing
                    C.checkSortExpr Nothing F.dummySpan environment identity @?= Just F.boolSort
                )
                [F.fromListSEnv declarations | declarations <- [[("x", fractionalSort)], [("alpha", F.boolSort), ("x", fractionalSort)]]]
        , testGroup
            "local nominal coordinates retain their outer meaning"
            [ testCase (label ++ " / " ++ show kind ++ " / " ++ show valid) $ do
                let expression = enclose (F.PAll [("alpha", kind)] (F.EEq (F.EVar "value") rhs))
                isJust (C.checkSortExpr Nothing F.dummySpan mempty expression) @?= valid
                singleElaborate mempty expression >>= (@?= valid)
                result <- try (evaluate (force (C.elaborate numericParameter expression))) :: IO (Either SomeException F.Expr)
                either (const False) (const True) result @?= valid
            | let literal = F.ECon (F.L "nominal" fractionalSort)
            , (label, enclose) <-
                [ ("lambda", F.ELam ("value", fractionalSort))
                , ("universal", F.PAll [("value", fractionalSort)])
                , ("existential", F.PExist [("value", fractionalSort)])
                , ("annotated let", F.ELet "value" literal)
                , ("inferred conditional let", F.ELet "value" (F.EIte F.PTrue literal literal))
                , ("inferred application let", F.ELet "value" (F.EApp (F.ELam ("argument", fractionalSort) (F.EVar "argument")) literal))
                , ("inferred function let", \body -> F.ELet "function" (F.ELam ("argument", F.FInt) literal) (F.subst1 body ("value", F.EApp (F.EVar "function") (numericInt 0))))
                ]
            , kind <- [F.FNum, F.FFrac]
            , (valid, rhs) <- [(True, F.EVar "value"), (False, numericInt 0)]
            ]
        , testCase "annotation closure is idempotent and retains implicit KVar actuals" $ do
            let expression = F.PAll [("alpha", F.boolSort)] (F.PKVar (F.KV "k") (M.singleton "owned" fractionalSort) mempty)
                elaborateAt = C.elabExpr numericParameter{C.epEnv = fractionalEnvironment} Nothing
                normalized = elaborateAt expression
            elaborateAt normalized @?= normalized
            case normalized of
                F.PAll [(name, sort)] (F.PKVar _ types actuals) -> do
                    name @?= "alpha"
                    sort @?= F.boolSort
                    M.lookup "owned" types @?= Just F.FReal
                    F.fromKVarSubst actuals @?= M.empty
                other -> assertFailure (show other)
        , testCase "quantified annotations retain their ambient kind after term alpha-renaming" $ do
            let expression = F.PAll [("alpha", F.FFrac), ("x", fractionalSort)] (F.PAtom F.Eq (F.EVar "x") (F.ECst (F.EVar "x") fractionalSort))
                environment = F.fromListSEnv [("alpha", F.FNum)]
                elaborateAt = C.elabExpr numericParameter{C.epEnv = F.emptySymEnv{F.seSort = environment}} Nothing
                normalized = elaborateAt expression
                renamed = F.substr (S.fromList ["alpha"]) (F.mkSubst []) expression
            elaborateAt normalized @?= normalized
            map (C.checkSortExpr Nothing F.dummySpan environment) [normalized, elaborateAt renamed] @?= replicate 2 (Just F.boolSort)
            case normalized of
                F.PAll [(name, F.FFrac), ("x", F.FInt)] (F.PAtom F.Eq _ (F.ECst _ F.FInt)) -> name @?= "alpha"
                other -> assertFailure (show other)
        , testCase "duplicate source binders do not become distinct valid binders" $ do
            let bindings = [("alpha", F.FFrac), ("alpha", F.FNum)]
                expression = F.PAll bindings (F.ECst F.PTrue fractionalSort)
            C.checkSortExpr Nothing F.dummySpan (F.seSort fractionalEnvironment) expression @?= Nothing
            case C.elabExpr numericParameter{C.epEnv = fractionalEnvironment} Nothing (F.PAll bindings F.PTrue) of
                F.PAll [(first, F.FFrac), (second, F.FNum)] _ -> first @?= second
                other -> assertFailure (show other)
        , testCase "opaque KVar annotations close without validating or deleting actuals" $ do
            let actual = F.ECst F.PTrue fractionalSort
                expression = F.PAll [("alpha", F.FFrac)] (F.PKVar (F.KV "k") mempty (F.toKVarSubst (M.singleton "argument" actual)))
                parameter = numericParameter{C.epEnv = F.emptySymEnv{F.seSort = F.fromListSEnv [("alpha", F.FNum)]}}
            case C.elabExpr parameter Nothing expression of
                F.PAll _ (F.PKVar _ _ actuals) -> M.lookup "argument" (F.fromKVarSubst actuals) @?= Just (F.ECst F.PTrue F.FInt)
                other -> assertFailure (show other)
        , testCase "defined-function parameters do not reinterpret free declarations" $
            withSMT fractionalEnvironment $ do
                let definition = F.Equ "halfGlobal" [("alpha", F.FNum)] (F.EBin F.Div (F.EVar "x") (numericInt 2)) F.FReal False
                    F.MkDefinedFuns [elaborated] = C.elaborate (numericParameter{C.epEnv = fractionalEnvironment}) (F.MkDefinedFuns [definition])
                SMT.smtDecl "x" fractionalSort
                SMT.smtAssert (F.PAtom F.Eq (F.EVar "x") (numericReal 1))
                SMT.smtDefineFunc (F.eqName elaborated) (F.eqArgs elaborated) (F.eqSort elaborated) (F.eqBody elaborated)
                inhabited <- SMT.command SMT.CheckSat
                SMT.smtAssert (F.PNot (F.PAtom F.Eq (F.EApp (F.EVar "halfGlobal") (numericInt 0)) (numericReal 0.5)))
                actual <- SMT.command SMT.CheckSat
                liftIO $ do
                    inhabited @?= SMT.Sat
                    actual @?= SMT.Unsat
        , testCase "deferred native function instances retain their ambient fractional carrier" $ do
            let native = Theory.theorySymbols Config.Z3
                environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("alpha", F.FFrac)] <> fmap F.tsSort native, F.seTheory = native}
                function = F.FFunc F.boolSort (F.arraySort fractionalSort F.boolSort)
                selected = F.ECoerc function function (F.ECst (F.EVar Theory.arrConstM) function)
                direct = F.EApp (F.ECst (F.EVar Theory.arrConstM) function) F.PTrue
                expression = F.PAll [("alpha", F.FNum)] (F.PAtom F.Eq (F.EApp selected F.PTrue) direct)
                elaborated = C.elaborate (numericParameter{C.epEnv = environment}) expression
            withSMT environment $ do
                -- The default proof-search setup disables quantified model finding.
                SMT.smtSetMbqi
                inhabited <- SMT.smtBracket "native identity inhabitation" (SMT.smtAssert elaborated >> SMT.command SMT.CheckSat)
                SMT.smtAssert (F.PNot elaborated)
                actual <- SMT.command SMT.CheckSat
                liftIO $ do
                    inhabited @?= SMT.Sat
                    actual @?= SMT.Unsat
        , testCase "deferred native instances retain an ambient nominal carrier and countermodels" $ do
            let native = Theory.theorySymbols Config.Z3
                environment = F.emptySymEnv{F.seSort = fmap F.tsSort native, F.seTheory = native}
                function = F.FFunc F.boolSort (F.arraySort fractionalSort F.boolSort)
                selected = F.ECoerc function function (F.ECst (F.EVar Theory.arrConstM) function)
                expression other =
                    F.PAll
                        [("alpha", F.FFrac)]
                        (F.PAtom F.Eq (F.EApp selected F.PTrue) (F.EApp (F.ECst (F.EVar Theory.arrConstM) function) other))
            mapM_
                ( \(other, expected) ->
                    withSMT environment $ do
                        let elaborated = C.elaborate (numericParameter{C.epEnv = environment}) (expression other)
                        actual <- SMT.smtSetMbqi >> SMT.smtAssert (F.PNot elaborated) >> SMT.command SMT.CheckSat
                        liftIO (assertEqual (show other) expected actual)
                )
                [(F.PTrue, SMT.Unsat), (F.PFalse, SMT.Sat)]
        ]

numericScopeQuery :: F.SymEnv -> [(F.Symbol, F.Sort)] -> [F.Expr] -> F.Expr -> IO SMT.Response
numericScopeQuery environment declarations assumptions expression =
    withSMT environment $ do
        SMT.smtDecls declarations
        mapM_ SMT.smtAssert assumptions
        SMT.smtAssert (C.elabExpr (numericParameter{C.epEnv = environment}) (Just F.boolSort) expression)
        SMT.command SMT.CheckSat

withSMT :: F.SymEnv -> StateT SMT.Context IO a -> IO a
withSMT environment action =
    bracket (SMT.makeContextNoLog Config.defConfig{Config.solver = Config.Z3}) SMT.cleanupContext $ \context ->
        evalStateT action context{SMT.ctxSymEnv = environment}

binderNormalizationTests :: TestTree
binderNormalizationTests =
    testGroup "binder sort normalization" $
        [ testGroup
            label
            [ testCase "universal identity is valid" $
                check (F.PNot (F.PAll [("x", source)] identity)) SMT.Unsat
            , testCase "independent container values need not be equal" $
                check (F.PNot (F.PAll [("x", source), ("y", source)] (F.PAtom F.Eq x (F.ECst (F.EVar "y") source)))) SMT.Sat
            , testCase "existential identity remains inhabited" $
                check (F.PExist [("x", source)] identity) SMT.Sat
            ]
        | (label, source) <-
            [ ("set", F.setSort F.FInt)
            , ("map with nested set", F.mapSort F.FInt (F.setSort F.FInt))
            ]
        , let identity = F.PAtom F.Eq x (F.ECst x source)
        ]
  where
    x = F.EVar "x"
    parameter = C.ElabParam (Config.ElabFlags True False) "binder normalization regression" F.emptySymEnv
    check expression expected =
        withSMT F.emptySymEnv $ do
            actual <- SMT.smtAssert (C.elaborate parameter expression) >> SMT.command SMT.CheckSat
            liftIO (actual @?= expected)

numericTests :: TestTree
numericTests =
    testGroup
        "numeric operator carrier judgments"
        [ testCase "all scalar operand combinations retain their mathematical result" $
            mapM_
                ( \(operator, left, right, expected) -> do
                    let expression = F.EBin operator left right
                    C.checkSortExpr Nothing F.dummySpan mempty expression @?= expected
                    case expected of
                        Nothing -> pure ()
                        Just result -> do
                            C.sortExpr Nothing F.dummySpan mempty (F.ELet "result" expression (F.EVar "result")) @?= result
                            _ <- evaluate (force (C.elabExpr numericParameter (Just result) expression))
                            pure ()
                )
                numericCases
        , testCase "Boolean operands remain rejected in both positions" $
            mapM_
                (\(operator, left, right) -> C.checkSortExpr Nothing F.dummySpan mempty (F.EBin operator left right) @?= Nothing)
                [(operator, left, right) | operator <- numericOperators, (left, right) <- [(F.PTrue, numericInt 2), (numericInt 2, F.PTrue)]]
        , testCase "real division cannot initialize an integer result" $ do
            let half = F.EBin F.RDiv (numericInt 1) (numericInt 2)
            C.checkSortExpr Nothing F.dummySpan mempty (F.ECst half F.FInt) @?= Nothing
            result <- elaborateResult numericParameter (Just F.FInt) half
            assertBool "real division acquired an integer result" (either (const True) (const False) result)
        , testCase "elaboration selects the native operator for either real operand" $
            mapM_
                ( \(operator, left, right, expected) -> case C.elabExpr numericParameter Nothing (F.EBin operator left right) of
                    F.EBin actual _ _ -> actual @?= expected
                    other -> assertFailure ("unexpected numeric elaboration: " ++ show other)
                )
                [ (operator, left, right, if operator == F.Times then F.RTimes else F.RDiv)
                | operator <- [F.Times, F.Div]
                , (left, right) <- [(numericInt 1, numericReal 2), (numericReal 1, numericInt 2), (numericReal 1, numericReal 2)]
                ]
        , testCase "nominal numeric metadata does not invent a Real SMT carrier" $ do
            let nominal = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc "Numeric") True True)
                environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("left", nominal), ("right", nominal)]}
                parameter = numericParameter{C.epEnv = environment}
                expression = F.EBin F.Div (F.EVar "left") (F.EVar "right")
            C.checkSortExpr Nothing F.dummySpan (F.seSort environment) expression @?= Just nominal
            case C.elabExpr parameter Nothing expression of
                F.EBin actual _ _ -> actual @?= F.Div
                other -> assertFailure ("unexpected nominal elaboration: " ++ show other)
        , testCase "fractional kind premises determine scalar and compound carriers" $ do
            F.sortSmtSort False fractionalEnvironment fractionalSort @?= F.SReal
            F.sortSmtSort False fractionalEnvironment (F.arraySort fractionalSort F.boolSort) @?= F.SArray F.SReal F.SBool
            F.sortSmtSort False fractionalEnvironment (F.setSort fractionalSort) @?= F.SSet F.SReal
            F.sortSmtSort False F.emptySymEnv fractionalSort @?= F.SInt
            F.sortSmtSort False (F.emptySymEnv{F.seSort = F.fromListSEnv [("alpha", F.FNum)]}) fractionalSort @?= F.SInt
        , testCase "fractional modulo is refused at the sort judgment" $
            C.checkSortExpr Nothing F.dummySpan (F.seSort fractionalEnvironment) (F.EBin F.Mod (F.EVar "x") (F.EVar "y")) @?= Nothing
        , testCase "fractional values cannot narrow to integer scalars or arrays" $ do
            let array = F.arraySort fractionalSort F.boolSort
                environment = F.insertSEnv "array" array (F.seSort fractionalEnvironment)
            C.checkSortExpr Nothing F.dummySpan environment (F.ECst (F.EVar "x") F.FInt) @?= Nothing
            C.checkSortExpr Nothing F.dummySpan environment (F.ECst (F.EVar "array") (F.arraySort F.FInt F.boolSort)) @?= Nothing
            C.checkSortExpr Nothing F.dummySpan environment (F.ECst (numericInt 1) fractionalSort) @?= Just F.FReal
            C.checkSortExpr Nothing F.dummySpan environment (F.EBin F.Plus (F.EVar "x") (numericInt 1)) @?= Just F.FReal
        , testCase "deferred carrier comparisons retain their declaration kind scope" $ do
            let scoped kind = F.PAll [("alpha", kind), ("left", F.arraySort fractionalSort F.boolSort), ("right", F.arraySort F.FInt F.boolSort)] (F.PAtom F.Ueq (F.EVar "left") (F.EVar "right"))
            singleElaborate (F.seSort fractionalEnvironment) (scoped F.FNum) >>= (@?= False)
            singleElaborate (F.fromListSEnv [("alpha", F.FNum)]) (scoped F.FFrac) >>= (@?= True)
        , testGroup
            "declaration-owned fractional judgments survive term scopes"
            [ testCase label $ do
                let environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("alpha", outer)]}
                    expression = F.PAll [("alpha", inner), ("x", fractionalSort), ("y", fractionalSort)] body
                    elaborated = C.elabExpr (numericParameter{C.epEnv = environment}) (Just F.boolSort) expression
                withSMT environment $ do
                    SMT.smtAssert (F.PNot elaborated)
                    actual <- SMT.command SMT.CheckSat
                    after <- gets (F.seSort . SMT.ctxSymEnv)
                    liftIO $ do
                        actual @?= expected
                        after @?= F.seSort environment
            | (label, outer, inner, body, expected) <- fractionalScopeCases
            ]
        , testCase "fractional division retains an inhabited result and its field law" $
            withSMT fractionalEnvironment $ do
                let parameter = numericParameter{C.epEnv = fractionalEnvironment}
                    division = F.EBin F.Div (F.EVar "x") (F.EVar "y")
                    identity = F.PAtom F.Eq (F.EBin F.Times division (F.EVar "y")) (F.EVar "x")
                liftIO (C.checkSortExpr Nothing F.dummySpan (F.seSort fractionalEnvironment) division @?= Just F.FReal)
                SMT.smtDecls [("x", fractionalSort), ("y", fractionalSort), ("result", fractionalSort)]
                SMT.smtAssert (F.PAtom F.Eq (F.EVar "x") (numericReal 1))
                SMT.smtAssert (F.PAtom F.Eq (F.EVar "y") (numericReal 2))
                SMT.smtDefineFunc "fractionalIdentity" [("argument", fractionalSort)] fractionalSort (F.EVar "argument")
                let defined = F.EApp (F.EVar "fractionalIdentity") (C.elabExpr parameter (Just fractionalSort) division)
                SMT.smtAssert (F.PAtom F.Eq (F.EVar "result") defined)
                inhabited <- SMT.command SMT.CheckSat
                SMT.smtAssert (F.PNot (C.elabExpr parameter (Just F.boolSort) identity))
                wrong <- SMT.command SMT.CheckSat
                liftIO $ do
                    inhabited @?= SMT.Sat
                    wrong @?= SMT.Unsat
        , testGroup
            "actual SMT result is inhabited and has the expected value"
            [ testCase label $
                withSMT F.emptySymEnv $ do
                    let resultSort = C.sortExpr Nothing F.dummySpan mempty expression
                        elaborated = C.elabExpr numericParameter (Just resultSort) expression
                    SMT.smtDecl "delayedNumeric" resultSort
                    SMT.smtAssert (F.PAtom F.Eq (F.EVar "delayedNumeric") elaborated)
                    inhabited <- SMT.command SMT.CheckSat
                    SMT.smtAssert (F.PNot (F.PAtom F.Eq (F.EVar "delayedNumeric") expected))
                    wrong <- SMT.command SMT.CheckSat
                    liftIO $ do
                        inhabited @?= SMT.Sat
                        wrong @?= SMT.Unsat
            | (label, expression, expected) <-
                [ ("integer operands of real division", F.EBin F.RDiv (numericInt 1) (numericInt 2), numericReal 0.5)
                , ("mixed multiplication", F.EBin F.Times (numericInt 3) (numericReal 0.5), numericReal 1.5)
                , ("reversed mixed multiplication", F.EBin F.Times (numericReal 0.5) (numericInt 3), numericReal 1.5)
                , ("mixed division", F.EBin F.Div (numericInt 1) (numericReal 2), numericReal 0.5)
                , ("reversed mixed division", F.EBin F.Div (numericReal 1) (numericInt 2), numericReal 0.5)
                , ("integer division stays integer", F.EBin F.Div (numericInt 7) (numericInt 3), numericInt 2)
                , ("integer modulo stays Euclidean", F.EBin F.Mod (numericInt (-7)) (numericInt 3), numericInt 2)
                ]
            ]
        ]

numericOperators :: [F.Bop]
numericOperators = [F.Plus, F.Minus, F.Times, F.Div, F.Mod, F.RTimes, F.RDiv]

fractionalSort :: F.Sort
fractionalSort = F.FObj "alpha"

fractionalEnvironment :: F.SymEnv
fractionalEnvironment = F.emptySymEnv{F.seSort = F.fromListSEnv [("alpha", F.FFrac), ("x", fractionalSort), ("y", fractionalSort)]}

fractionalScopeCases :: [(String, F.Sort, F.Sort, F.Expr, SMT.Response)]
fractionalScopeCases =
    [ ("fractional declaration survives a numeric term binder", F.FFrac, F.FNum, identity x, SMT.Unsat)
    , ("fractional field law still admits an incorrect-result countermodel", F.FFrac, F.FNum, identity (F.EBin F.Plus x (numericInt 1)), SMT.Sat)
    , ("numeric declaration survives a fractional term binder", F.FNum, F.FFrac, F.PImp (F.PAnd [F.PAtom F.Eq x (numericInt 1), F.PAtom F.Eq y (numericInt 2)]) (F.PAtom F.Eq division (numericInt 0)), SMT.Unsat)
    ]
  where
    x = F.EVar "x"
    y = F.EVar "y"
    division = F.EBin F.Div x y
    identity result = F.PImp (F.PAtom F.Ne y (numericInt 0)) (F.PAtom F.Eq (F.EBin F.Times division y) result)

numericCases :: [(F.Bop, F.Expr, F.Expr, Maybe F.Sort)]
numericCases =
    [ (operator, left, right, result operator leftSort rightSort)
    | operator <- numericOperators
    , (left, leftSort) <- [(numericInt 1, F.FInt), (numericReal 1, F.FReal)]
    , (right, rightSort) <- [(numericInt 2, F.FInt), (numericReal 2, F.FReal)]
    ]
  where
    result F.Mod left right | left /= F.FInt || right /= F.FInt = Nothing
    result F.RDiv _ _ = Just F.FReal
    result _ left right = Just (if left == F.FReal || right == F.FReal then F.FReal else F.FInt)

numericParameter :: C.ElabParam
numericParameter = C.ElabParam (Config.ElabFlags False False) "numeric operator regression" F.emptySymEnv

numericInt :: Integer -> F.Expr
numericInt = F.ECon . F.I

numericReal :: Double -> F.Expr
numericReal = F.ECon . F.R

unificationTests :: TestTree
unificationTests = testCase "shared unification equations and lexical schemes" $ do
    mapM_
        (\(label, left, right, expected) -> assertEqual label expected (isJust (C.unifySorts left right)))
        [ ("forall label 0 with free input coordinate 42 is accepted", F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 42)), F.FFunc F.boolSort F.FInt, True)
        , ("alpha-renamed label 1 with same free coordinate is accepted", F.FAbs 1 (F.FFunc (F.FVar 1) (F.FVar 42)), F.FFunc F.boolSort F.FInt, True)
        , ("direct infinite equation is refused", F.FVar 0, F.FFunc (F.FVar 0) F.FInt, False)
        , ("indirect infinite equation is refused", F.FFunc (F.FVar 0) (F.FVar 1), F.FFunc (F.FVar 1) (F.FFunc (F.FVar 0) F.FInt), False)
        , ("later alias cannot overwrite an established incompatible binding", F.FFunc (F.FVar 0) (F.FFunc (F.FVar 1) (F.FVar 0)), F.FFunc (F.FVar 1) (F.FFunc F.FInt F.boolSort), False)
        , ("self variable equation is permitted", F.FVar 0, F.FVar 0, True)
        , ("closed scheme can be bound as a whole without a false occurs failure", F.FVar 0, F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 0)), True)
        , ("whole scheme is independently instantiated at later occurrences", F.FFunc (F.FVar 8) (F.FFunc (F.FVar 8) (F.FVar 8)), F.FFunc identityScheme (F.FFunc identityBool (F.FFunc identityBool identityBool)), True)
        , ("negative forall binder is lexically bound", F.FAbs (-1) (F.FFunc (F.FVar (-1)) (F.FVar (-1))), F.FFunc F.boolSort F.boolSort, True)
        , ("largest forall label does not control fresh supply", F.FAbs maxBound (F.FFunc (F.FVar maxBound) (F.FVar 0)), F.FFunc F.boolSort F.FInt, True)
        ]
    mapM_
        (\(label, aliases, left, right, valid) -> assertEqual label valid (isJust (C.unifyFast False (C.mkSearchEnv (F.fromListSEnv aliases)) left right)))
        [ ("self declaration alias is refused", [("A", F.FObj "A")], F.FObj "A", F.boolSort, False)
        , ("mutual declaration aliases are refused", [("A", F.FObj "B"), ("B", F.FObj "A")], F.FObj "A", F.boolSort, False)
        , ("structural alias cycle is refused", [("A", F.FFunc (F.FObj "A") F.boolSort)], F.FObj "A", F.FFunc F.boolSort F.boolSort, False)
        , ("acyclic alias chain is accepted", [("A", F.FObj "B"), ("B", F.boolSort)], F.FObj "A", F.boolSort, True)
        , ("opposite operands have independent acyclic paths", [("A", F.boolSort), ("B", F.FObj "A")], F.FObj "A", F.FObj "B", True)
        , ("acyclic sibling alias uses are independent", [("A", F.boolSort)], F.FFunc (F.FObj "A") (F.FObj "A"), F.FFunc F.boolSort F.boolSort, True)
        , ("unused cyclic alias does not change a reflexive judgment", [("A", F.FObj "A")], F.boolSort, F.boolSort, True)
        ]
    case C.unifySorts (F.FFunc (F.FVar 0) (F.FVar 1)) (F.FFunc (F.FVar 1) F.FInt) of
        Nothing -> fail "finite alias chain unexpectedly refused"
        Just substitution -> do
            assertEqual "transitive substitution resolves initial alias" F.FInt (C.apply substitution (F.FVar 0))
            assertEqual
                "returned solution application is idempotent"
                (C.apply substitution (F.FVar 0))
                (C.apply substitution (C.apply substitution (F.FVar 0)))
    case C.unifySorts (F.FVar 0) F.FInt of
        Nothing -> fail "simple variable equation unexpectedly refused"
        Just substitution ->
            assertEqual
                "substitution masks a lexically bound variable"
                (F.FAbs 0 (F.FVar 0))
                (C.apply substitution (F.FAbs 0 (F.FVar 0)))
    case C.unifySorts (F.FVar 0) (F.FVar 1) of
        Nothing -> fail "simple alias unexpectedly refused"
        Just substitution -> do
            let result = C.apply substitution (F.FAbs 1 (F.FFunc (F.FVar 0) (F.FVar 1)))
            assertEqual "free substitution image remains free below forall" [1] (unificationFree [] result)
    assertEqual "forall immediate variable body is not monomorphic" False $
        C.isMono (F.FAbs 0 (F.FVar 0))
    case C.unifyFast False (C.mkSearchEnv siblingAliasEnv) (F.FObj "Alias") (F.FFunc F.FInt F.boolSort) of
        Nothing -> fail "demand-discovered alias lost its independent result coordinate"
        Just substitution ->
            assertEqual
                "opening an alias domain preserves its free result coordinate"
                F.boolSort
                (C.apply substitution (F.FVar 0))
    case C.unifyFastWith
        (S.singleton 0)
        False
        (C.mkSearchEnv aliasEnv)
        (F.FObj "Alias")
        (F.FAbs 7 (F.FFunc (F.FVar 7) F.FInt)) of
        Nothing -> fail "reserved alias coordinate unexpectedly refused"
        Just substitution -> case C.apply substitution (F.FVar 0) of
            F.FFunc (F.FVar input) F.FInt -> assertEqual "alias coordinate cannot be chosen by forall opening" True (input /= 0)
            other -> fail ("unexpected alias solution " ++ show other)
    case C.unifyFastWith
        (S.singleton 0)
        False
        (C.mkSearchEnv mempty)
        (F.FFunc (F.FVar 4) F.FInt)
        (F.FAbs 7 (F.FFunc (F.FFunc (F.FVar 7) (F.FVar 7)) F.FInt)) of
        Nothing -> fail "reserved later coordinate unexpectedly refused"
        Just substitution -> do
            assertEqual "fresh image does not alias a later caller coordinate" False $
                0 `elem` unificationFree [] (C.apply substitution (F.FVar 4))
            assertEqual "later caller coordinate remains independent" (F.FVar 0) (C.apply substitution (F.FVar 0))
    mapM_
        (\(label, final, expected) -> assertEqual label expected (C.unifyTo1 (C.mkSearchEnv mempty) [F.FVar 0, F.FFunc (F.FVar 1) F.FInt, final]))
        [ ("unifyTo1 returns the final transitive solution", F.FFunc F.boolSort F.FInt, Just (F.FFunc F.boolSort F.FInt))
        , ("unifyTo1 rejects a later conflicting result", F.FFunc F.boolSort F.boolSort, Nothing)
        ]
    assertEqual "alias unification reserves the complete caller environment" True $
        isJust
            ( C.unifyFastWith
                (C.sortFieldIndices aliasEnv)
                False
                (C.mkSearchEnv aliasEnv)
                (F.FObj "Alias")
                (F.FAbs 7 (F.FFunc (F.FVar 7) F.FInt))
            )
    let batch =
            jointSorts
                (F.fromListSEnv [("make", F.FAbs 7 (F.FFunc F.FInt (F.FVar 7)))])
                (F.fromListSEnv [("receiving", F.FVar 0)])
                [F.EApp (F.EVar "make") (F.ECon (F.I 1)), F.EApp (F.EVar "make") (F.ECon (F.I 2))]
    case batch of
        Right [F.FVar first, F.FVar second] -> do
            assertEqual "batch occurrences open independent result coordinates" True (first /= second)
            assertEqual "batch result coordinates avoid receiving judgment" True (first /= 0 && second /= 0)
        other -> fail ("unexpected batch result " ++ show other)
    let openingBody negative bound = F.FFunc negative (F.FFunc bound (F.FAbs 5 (F.FFunc negative (F.FVar 5))))
        openingEnvironment =
            F.fromListSEnv
                [ ("repeated", F.FAbs 5 (F.FAbs 5 (openingBody (F.FVar (-1)) (F.FVar 5))))
                , ("next", F.FAbs 7 (F.FVar 7))
                ]
    assertEqual
        "scheme opening preserves negative, repeated, nested, and subsequent coordinates"
        (Right [openingBody (F.FVar 0) (F.FVar 1), F.FVar 3])
        (jointSorts openingEnvironment mempty [F.EVar "repeated", F.EVar "next"])
    deferredBool <-
        unificationElaborateAt (F.FVar 9) $
            F.ELet "unused" (F.PAtom F.Ueq (F.EVar "f") F.PTrue) (F.EVar "f")
    assertEqual "deferred native equality accepts the final Boolean coordinate" True $
        either (const False) (const True) deferredBool
    assertEqual "direct checker defers Boolean classification until the complete equation solution" (Just F.boolSort) $
        C.checkSortExpr
            Nothing
            F.dummySpan
            (F.fromListSEnv [("f", F.FVar 9)])
            (F.ELet "unused" (F.PAtom F.Ueq (F.EVar "f") F.PTrue) (F.ECst (F.EVar "f") F.boolSort))
    let numeric name capability = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc name) capability False)
        ordered = F.PAtom F.Le (F.EVar "apple") (F.EVar "banana")
        numericEnvironment bananaCapability =
            F.fromListSEnv
                [ ("apple", numeric "Apple" True)
                , ("banana", numeric "Banana" bananaCapability)
                ]
    assertEqual "distinct declared numeric sorts support ordering" (Just F.boolSort) $
        C.checkSortExpr Nothing F.dummySpan (numericEnvironment True) ordered
    assertEqual "an integer representation does not confer numeric capability" Nothing $
        C.checkSortExpr Nothing F.dummySpan (numericEnvironment False) ordered
    assertEqual "earlier let annotations reflect later equations on shared caller coordinates" (Right [F.boolSort, F.boolSort]) $
        jointSorts
            (F.fromListSEnv [("x", F.FVar 9), ("consume", F.FFunc F.boolSort F.boolSort)])
            mempty
            [F.EVar "x", F.EApp (F.EVar "consume") (F.EVar "x")]
    mapM_
        (\(label, expression, expected) -> assertEqual label expected (C.exprSortMaybe expression))
        [ ("annotated application opens forall apart from free argument index", F.EApp (annotated (F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 0)))) (annotated (F.FFunc (F.FVar 0) F.FInt)), Just (F.FFunc (F.FVar 0) F.FInt))
        , ("annotated application rejects an incompatible argument", F.EApp (annotated (F.FFunc F.boolSort F.FInt)) (annotated F.FInt), Nothing)
        , ("annotated application refuses an unavailable nominal alias", F.EApp (annotated (F.FFunc (F.FObj "Missing") F.FInt)) (annotated F.boolSort), Nothing)
        , ("annotated application does not invent a function shape", F.EApp (annotated (F.FVar 0)) (annotated F.FInt), Nothing)
        , ("annotated lambda retains its body equation on the domain", F.ELam ("x", F.FVar 9) (F.EApp (annotated (F.FFunc F.boolSort F.boolSort)) (annotated (F.FVar 9))), Just (F.FFunc F.boolSort F.boolSort))
        ]
    let lambda = F.ELam ("x", F.FVar 9) (F.EApp (F.EVar "f") (F.EVar "x"))
        parameters =
            C.ElabParam
                (Config.ElabFlags False False)
                (F.dummyLoc "lambda consistency")
                F.emptySymEnv{F.seSort = F.fromListSEnv [("f", F.FFunc F.boolSort F.boolSort)]}
    case C.elabExpr parameters Nothing lambda of
        F.ELam (_, domain) (F.ECst (F.EApp _ (F.ECst (F.EVar "x") occurrence)) result) -> do
            assertEqual "elaboration substitutes the lambda domain" F.boolSort domain
            assertEqual "lambda binder and occurrence have one solved carrier" domain occurrence
            assertEqual "elaboration retains the lambda result" F.boolSort result
        other -> fail ("unexpected elaborated lambda " ++ show other)
  where
    identityScheme = F.FAbs 2 (F.FFunc (F.FVar 2) (F.FVar 2))
    identityBool = F.FFunc F.boolSort F.boolSort
    aliasEnv = F.fromListSEnv [("Alias", F.FVar 0)]
    siblingAliasEnv = F.fromListSEnv [("Alias", F.FFunc (F.FAbs 7 (F.FVar 7)) (F.FVar 0))]
    annotated = F.ECst (F.EVar "annotation")

unificationElaborateAt :: F.Sort -> F.Expr -> IO (Either SomeException F.Expr)
unificationElaborateAt sort expression =
    elaborateResult
        (C.ElabParam (Config.ElabFlags False False) (F.dummyLoc "unification regression") F.emptySymEnv{F.seSort = F.fromListSEnv [("f", sort)]})
        (Just F.boolSort)
        expression

elaborateResult :: C.ElabParam -> Maybe F.Sort -> F.Expr -> IO (Either SomeException F.Expr)
elaborateResult parameter expected = try . evaluate . force . C.elabExpr parameter expected

checkElaboration :: F.Located String -> [(F.Symbol, F.Sort)] -> Maybe F.Sort -> F.Expr -> Bool -> IO ()
checkElaboration message bindings expectedSort expression expected = do
    let parameter = C.ElabParam (Config.solverFlags Config.defConfig) message F.emptySymEnv{F.seSort = F.fromListSEnv bindings}
    outcome <- elaborateResult parameter expectedSort expression
    assertEqual (show outcome) expected (either (const False) (const True) outcome)

unificationFree :: [Int] -> F.Sort -> [Int]
unificationFree bound (F.FVar n) = [n | n `notElem` bound]
unificationFree bound (F.FAbs n body) = unificationFree (n : bound) body
unificationFree bound (F.FFunc argument result) = unificationFree bound argument ++ unificationFree bound result
unificationFree bound (F.FApp function argument) = unificationFree bound function ++ unificationFree bound argument
unificationFree _ _ = []

nativeTests :: TestTree
nativeTests =
    testGroup
        "native equality carriers"
        ( [ testCase (label ++ " " ++ show relation) $ do
                let expression = F.PAtom relation (F.EVar "left") (F.EVar "right")
                checkElaboration "native equality" [("left", left), ("right", right)] Nothing expression expected
          | (label, left, right, expected) <- nativeCases
          , relation <- [F.Ueq, F.Une]
          ]
            ++ [ testCase ("generic judgment " ++ label ++ " " ++ show relation) $ do
                    let environment = F.fromListSEnv [("left", left), ("right", right)]
                        expression = F.PAtom relation (F.EVar "left") (F.EVar "right")
                    (isJust (C.checkSortExpr Nothing F.dummySpan environment expression)) @?= expected
               | (label, left, right, expected) <- nativeCases
               , relation <- [F.Ueq, F.Une]
               , label `elem` ["same integers", "same sets", "set is not integer", "set is not bag", "Boolean is not integer"]
               ]
            ++ [ testCase ("configured source-head check " ++ label ++ " " ++ show relation) $ do
                    let environment = F.fromListSEnv [("left", left), ("right", right)]
                        expression = F.PAtom relation (F.EVar "left") (F.EVar "right") :: F.Expr
                        checked = runReader (C.checkSorted Nothing F.dummySpan environment expression) (Config.ElabFlags True False)
                    assertEqual label expected (isNothing checked)
               | (label, left, right, expected) <-
                    [ ("Set and Bag have distinct lowered ranges", F.setSort F.intSort, F.bagSort F.intSort, False)
                    , ("Set and its explicit Array carrier may compare", F.setSort F.intSort, F.arraySort F.intSort F.boolSort, True)
                    , ("Bag and its explicit Array carrier may compare", F.bagSort F.intSort, F.arraySort F.intSort F.intSort, True)
                    , ("Set and Int remain incompatible", F.setSort F.intSort, F.intSort, False)
                    ]
               , relation <- [F.Ueq, F.Une]
               ]
            ++ [ testCase ("opened aggregate parameter " ++ show relation) $ do
                    let concrete = F.setSort F.strSort
                        scheme = F.FAbs 0 (F.FFunc F.intSort (F.setSort (F.FVar 0)))
                        expression = F.PAtom relation (F.EVar "left") (F.EApp (F.EVar "wrap") (numericInt 1))
                    checkElaboration "opened aggregate equality" [("left", concrete), ("wrap", scheme)] Nothing expression True
               | relation <- [F.Ueq, F.Une]
               ]
            ++ [ testCase ("input-owned variable cannot change native carrier " ++ show relation) $ do
                    let expression = F.PAtom relation (F.EVar "left") (F.EVar "right")
                    checkElaboration "rigid native equality" [("left", F.FVar 7), ("right", F.strSort)] Nothing expression False
               | relation <- [F.Ueq, F.Une]
               ]
            ++ [mixedNativeInputs]
        )

mixedNativeInputs :: TestTree
mixedNativeInputs =
    testGroup
        "fresh aggregate selection preserves input source sorts"
        $ [ testCase ("carrier-changing input/" ++ show relation) $ do
                let concrete = F.arraySort F.boolSort F.boolSort
                    scheme = F.FAbs 42 (F.FFunc F.intSort (F.arraySort (F.FVar 0) (F.FVar 42)))
                    expression = F.PAtom relation (F.EVar "left") (F.EApp (F.EVar "wrap") (numericInt 1))
                checkElaboration "mixed aggregate equality" [("left", concrete), ("wrap", scheme)] Nothing expression False
          | relation <- [F.Ueq, F.Une]
          ]
            ++ [ testCase ("same-carrier function input/" ++ show relation) $ do
                    let concrete = F.arraySort (F.FFunc F.intSort F.intSort) F.strSort
                        scheme = F.FAbs 42 (F.FFunc F.intSort (F.arraySort (F.FVar 0) (F.FVar 42)))
                        environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("left", concrete), ("wrap", scheme), ("witness", F.FVar 0)]}
                        parameter = C.ElabParam (Config.solverFlags Config.defConfig) "same-carrier aggregate input" environment
                        expression = F.PAnd [F.PAtom relation (F.EVar "left") (F.EApp (F.EVar "wrap") (numericInt 1)), F.PAtom F.Eq (F.EVar "witness") (F.EVar "witness")]
                    outcome <- elaborateResult parameter Nothing expression
                    case outcome of
                        Right result -> case F.dropECst result of
                            F.PAnd [_, F.PAtom _ witness _] -> C.exprSortMaybe witness @?= Just (F.FVar 0)
                            _ -> assertFailure (show result)
                        Left failure -> assertFailure (show failure)
               | relation <- [F.Ueq, F.Une]
               ]
            ++ [ testCase (label ++ show relation ++ "/reverse=" ++ show reverseOperands) $ do
                    let concrete = F.arraySort (F.FVar 0) F.strSort
                        left = F.EVar "left"
                        right = F.EApp (F.EVar "wrap") (numericInt 1)
                        expression = if reverseOperands then F.PAtom relation right left else F.PAtom relation left right
                    checkElaboration message [("left", concrete), ("wrap", scheme)] Nothing expression True
               | (label, message, scheme) <-
                    [ ("fresh alias preserves caller coordinate/", "fresh aggregate alias", F.FAbs 41 (F.FAbs 42 (F.FFunc F.intSort (F.arraySort (F.FVar 41) (F.FVar 42)))))
                    , ("distinct caller coordinates/", "distinct aggregate inputs", F.FAbs 42 (F.FFunc F.intSort (F.arraySort (F.FVar 1) (F.FVar 42))))
                    ]
               , relation <- [F.Ueq, F.Une]
               , reverseOperands <- [False, True]
               ]

nativeCases :: [(String, F.Sort, F.Sort, Bool)]
nativeCases =
    [ ("same integers", F.intSort, F.intSort, True)
    , ("numeric embedding", F.intSort, F.realSort, True)
    , ("same sets", F.setSort F.intSort, F.setSort F.intSort, True)
    , ("set is not integer", F.setSort F.intSort, F.intSort, False)
    , ("set is not bag", F.setSort F.intSort, F.bagSort F.intSort, False)
    , ("aggregate indices do not numerically coerce", F.setSort F.intSort, F.setSort F.realSort, False)
    , ("nested aggregate carriers", F.setSort (F.setSort F.intSort), F.setSort F.intSort, False)
    , ("same strings", F.strSort, F.strSort, True)
    , ("string is not integer", F.strSort, F.intSort, False)
    , ("Boolean is not integer", F.boolSort, F.intSort, False)
    , ("erased nominal values", F.FObj "Alpha", F.FObj "Beta", True)
    , ("erased function values", F.FFunc F.intSort F.intSort, F.intSort, True)
    ]

-- Ascription cannot invent a representation conversion or lift numeric widening.
carrierTests :: TestTree
carrierTests =
    testGroup
        "elaboration carriers"
        $ [ testCase label $ do
                checkElaboration "carrier elaboration" bindings expectedSort expression expected
          | (label, bindings, expectedSort, expression, expected) <- carrierCases
          ]
            ++ [ testCase ("KVar actual source checking, explicit=" ++ show explicit) $ do
                    let flags = Config.ElabFlags True explicit
                        actual = F.ECst F.PTrue F.FInt
                        expression = F.PKVar (F.KV "opaque") mempty (F.mkKVarSubst [("argument", actual)])
                        parameter = C.ElabParam flags (F.atLoc F.dummySpan "demanded actual") F.emptySymEnv
                    C.checkSortExpr Nothing F.dummySpan mempty expression @?= Just F.boolSort
                    runReader (C.checkSorted Nothing F.dummySpan mempty expression) flags @?= Nothing
                    case C.elabExprE parameter Nothing expression of
                        Right result -> assertBool ("malformed demanded actual accepted: " ++ show result) (not explicit)
                        Left failure -> do
                            assertBool ("opaque actual was demanded: " ++ show failure) explicit
                            case F.errs failure of
                                [diagnostic] -> do
                                    F.errLoc diagnostic @?= F.dummySpan
                                    assertBool (show failure) ("Cannot cast" `isInfixOf` show (F.errMsg diagnostic))
                                _ -> assertFailure (show failure)
               | explicit <- [False, True]
               ]

carrierCases :: [(String, [(F.Symbol, F.Sort)], Maybe F.Sort, F.Expr, Bool)]
carrierCases =
    [ ("integer as real", [], Nothing, F.ECst one F.realSort, True)
    , ("real is not integer", [], Nothing, F.ECst half F.intSort, False)
    , ("same array", [("left", ints)], Nothing, F.ECst left ints, True)
    , ("array index has no numeric widening", [("left", ints)], Nothing, F.ECst left reals, False)
    , ("cast cannot hide array mismatch", [("left", ints), ("right", reals)], Nothing, F.PAtom F.Ueq (F.ECst left reals) right, False)
    , ("application result cannot fabricate array carrier", [("f", F.FFunc F.intSort ints), ("right", reals)], Nothing, F.PAtom F.Ueq (F.ECst call reals) right, False)
    , ("conditional result cannot fabricate array carrier", [("f", F.FFunc F.intSort ints)], Nothing, F.ECst (F.EIte F.PTrue call call) reals, False)
    , ("function domains do not numerically coerce", [("f", F.FFunc F.intSort F.intSort)], Nothing, F.ECst function (F.FFunc F.realSort F.intSort), False)
    , ("real consumer accepts integer", [("f", F.FFunc F.realSort F.realSort)], Nothing, call, True)
    , ("integer consumer rejects real", [("f", F.FFunc F.intSort F.intSort)], Nothing, F.EApp function half, False)
    , ("ascribed real cannot enter integer consumer", [("f", F.FFunc F.intSort F.intSort)], Nothing, F.EApp function (F.ECst half F.intSort), False)
    , ("explicit coercion checks source", [], Nothing, F.ECoerc F.boolSort F.intSort one, False)
    , ("explicit coercion keeps conversion", [], Nothing, F.ECoerc F.boolSort F.intSort F.PTrue, True)
    , ("carrier comparison uses final substitution", [("left", F.arraySort (F.FVar 7) F.boolSort), ("right", ints), ("result", F.FVar 7)], Just F.realSort, F.ELet "unused" (F.PAtom F.Ueq left right) (F.EVar "result"), False)
    , ("distinct numeric constructors may order", [("left", numeric "Apple"), ("right", numeric "Banana")], Nothing, F.PAtom F.Le left right, True)
    , ("integer carrier alone does not confer numeric capability", [("left", numeric "Apple"), ("right", F.FTC (F.symbolFTycon (F.dummyLoc "Banana")))], Nothing, F.PAtom F.Le left right, False)
    ]
  where
    ints = F.arraySort F.intSort F.boolSort
    reals = F.arraySort F.realSort F.boolSort
    left = F.EVar "left"
    right = F.EVar "right"
    function = F.EVar "f"
    one = F.ECon (F.I 1)
    half = F.ECon (F.R 1.5)
    call = F.EApp function one
    numeric name = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc name) True False)

reflexiveTests :: TestTree
reflexiveTests =
    testGroup "resolved reflexive unification" $
        [ testCase label (unchanged sort)
        | (label, sort) <-
            [ ("scheme self equation adds no coordinate equations", identity)
            , ("nested scheme self equation adds no coordinate equations", F.FFunc identity (F.FAbs 2 (F.FFunc (F.FVar 2) (F.FVar 9))))
            ]
        ]
            ++ [ testCase label $ assertEqual diagnostic expected (isJust (C.unifySorts left right))
               | (label, diagnostic, left, right, expected) <-
                    [ ("repeated solved scheme can open independently for Bool and Int", "scheme occurrences remain independent", F.FFunc (F.FVar 8) (F.FFunc (F.FVar 8) (F.FVar 8)), F.FFunc identity (F.FFunc booleanIdentity integerIdentity), True)
                    , ("a non-reflexive incompatible result is still refused", "incompatible instance was accepted", identity, F.FFunc F.FInt F.boolSort, False)
                    , ("infinite non-reflexive equation is still refused", "infinite equation was accepted", F.FVar 4, F.FFunc (F.FVar 4) F.FInt, False)
                    ]
               ]
            ++ [ testCase "non-reflexive free-variable constraint is retained" $
                    case C.unifySorts (F.FFunc (F.FVar 12) F.FInt) (F.FFunc F.boolSort F.FInt) of
                        Nothing -> assertFailure "finite equation was refused"
                        Just substitution -> C.apply substitution (F.FVar 12) @?= F.boolSort
               ]
  where
    identity = F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 0))
    booleanIdentity = F.FFunc F.boolSort F.boolSort
    integerIdentity = F.FFunc F.FInt F.FInt
    unchanged sort = case C.unifySorts sort sort of
        Nothing -> assertFailure "reflexive equation was refused"
        Just substitution ->
            map (C.apply substitution . F.FVar) [0 .. 16] @?= map F.FVar [0 .. 16]

seedTests :: TestTree
seedTests =
    testGroup "known solution conjunction" $
        [ testCase label $
            jointSorts seedEnvironment mempty inputs @?= Right expected
        | (label, inputs, expected) <-
            [ ("later input and result equations update earlier batch outputs", [seedApplication, F.ECst seedApplication F.FInt, seedX, F.ECst seedX F.boolSort], [F.FInt, F.FInt, F.boolSort, F.boolSort])
            , ("repeated solved applications retain their established carrier", [F.ECst seedApplication F.FInt, F.ECst seedX F.boolSort, seedApplication, seedApplication], [F.FInt, F.boolSort, F.FInt, F.FInt])
            ]
        ]
            ++ [ testCase label $ singleElaborate seedEnvironment (F.PAnd predicates) >>= (@?= expected)
               | (label, predicates, expected) <-
                    [ ("new conflicting result is not erased with an old solution", [seedEqual seedApplication seedOne, seedEqual seedApplication F.PTrue], False)
                    , ("new conflicting input is not erased with an old solution", [seedEqual seedApplication seedOne, seedEqual seedX F.PTrue, seedEqual (F.EApp seedFunction seedOne) seedOne], False)
                    , ("delayed native classification uses the completed Boolean solution", [F.PAtom F.Ueq seedX F.PTrue, seedEqual seedApplication seedOne, seedEqual seedX F.PTrue], True)
                    , ("delayed native classification rejects a completed integer solution", [F.PAtom F.Ueq seedX F.PTrue, seedEqual seedApplication seedOne, seedEqual seedX seedOne], False)
                    ]
               ]

seedEnvironment :: F.SEnv F.Sort
seedEnvironment = F.fromListSEnv [("function", F.FVar 7), ("x", F.FVar 9)]

seedFunction, seedX, seedApplication, seedOne :: F.Expr
seedFunction = F.EVar "function"
seedX = F.EVar "x"
seedApplication = F.EApp seedFunction seedX
seedOne = F.ECon (F.I 1)

seedEqual :: F.Expr -> F.Expr -> F.Expr
seedEqual = F.PAtom F.Eq

singleTests :: TestTree
singleTests =
    testGroup "single-visit sort judgments" $
        [ testCase label $ do
            C.checkSortExpr Nothing F.dummySpan singleEnvironment expression @?= if valid then Just F.boolSort else Nothing
            singleElaborate singleEnvironment expression >>= (@?= valid)
        | (label, expression, valid) <- singleCases
        ]
            ++ [ testCase "delayed native set equality keeps its solved carrier" $
                    singleElaborate singleCarrierEnvironment (F.PAnd [singleNativeSet, singleEquality singleX (F.EVar "setValue")]) >>= (@?= True)
               , testCase "delayed native set equality refuses a solved integer carrier" $
                    singleElaborate singleCarrierEnvironment (F.PAnd [singleNativeSet, singleEquality singleX singleOne]) >>= (@?= False)
               , testCase "doubling annotated application depth does not replay all descendants" $ do
                    small <- singleAllocation 4
                    large <- singleAllocation 8
                    assertBool "annotated application visits grow explosively" (large <= 16 * small + 2097152)
               ]

singleCases :: [(String, F.Expr, Bool)]
singleCases =
    [ ("expected result solves the earlier argument coordinate", F.PAnd [singleAsBoolean, singleEquality singleX F.PTrue], True)
    , ("expected result refuses a conflicting earlier argument coordinate", F.PAnd [singleAsBoolean, singleEquality singleX singleOne], False)
    , ("expected result solves an earlier free function result", F.PAnd [singleFreeBoolean, F.ECst (singleApp "function" F.PTrue) F.boolSort], True)
    , ("expected result refuses a conflicting free function result", F.PAnd [singleFreeBoolean, singleEquality (F.ECst (singleApp "function" singleOne) F.FInt) singleOne], False)
    , ("delayed native equality accepts the expected Boolean result", F.PAnd [F.PAtom F.Ueq singleX F.PTrue, singleAsBoolean], True)
    , ("delayed native equality rejects a subsequently solved integer", F.PAnd [F.PAtom F.Ueq singleX F.PTrue, singleEquality (F.ECst (singleApp "identity" singleX) F.FInt) singleOne], False)
    , ("polymorphic source occurrences still open independently", F.PAnd [singleApp "identity" F.PTrue, singleEquality (singleApp "identity" singleOne) singleOne], True)
    , ("invalid nested argument cast is not hidden by expected result", F.ECst (singleApp "identity" (F.ECst singleOne F.boolSort)) F.boolSort, False)
    , ("equality propagates an earlier free result equation", F.PAnd [singleEquality (singleApp "function" singleOne) singleOne, singleEquality (singleApp "function" singleOne) singleOne], True)
    , ("disequality cannot overwrite an earlier free result equation", F.PAnd [F.PAtom F.Ne (singleApp "function" singleOne) singleOne, singleEquality (singleApp "function" singleOne) F.PTrue], False)
    , ("disequality infers an unconstrained integer result", F.PAtom F.Ne (singleApp "function" singleOne) singleOne, True)
    ]

singleEnvironment :: F.SEnv F.Sort
singleEnvironment =
    F.fromListSEnv
        [ ("identity", F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 0)))
        , ("function", F.FVar 7)
        , ("x", F.FVar 9)
        ]

singleCarrierEnvironment :: F.SEnv F.Sort
singleCarrierEnvironment = F.insertSEnv "setValue" (F.setSort F.FInt) singleEnvironment

singleNativeSet, singleAsBoolean, singleFreeBoolean, singleX, singleOne :: F.Expr
singleNativeSet = F.PAtom F.Ueq singleX (F.EVar "setValue")
singleAsBoolean = F.ECst (singleApp "identity" singleX) F.boolSort
singleFreeBoolean = F.ECst (singleApp "function" singleX) F.boolSort
singleX = F.EVar "x"
singleOne = F.ECon (F.I 1)

singleApp :: F.Symbol -> F.Expr -> F.Expr
singleApp name = F.EApp (F.EVar name)

singleEquality :: F.Expr -> F.Expr -> F.Expr
singleEquality = F.PAtom F.Eq

singleElaborate :: F.SEnv F.Sort -> F.Expr -> IO Bool
singleElaborate declarations expression = do
    let parameter = C.ElabParam (Config.solverFlags Config.defConfig) "single-visit control" (F.emptySymEnv{F.seSort = declarations})
    result <- elaborateResult parameter Nothing expression
    pure (either (const False) (const True) result)

singleAllocation :: Int -> IO Integer
singleAllocation depth = do
    let identity :: F.Expr
        identity = F.ECst (F.EVar "identity") (F.FFunc F.FInt F.FInt)
        term = iterate (\argument -> F.ECst (F.EApp identity argument) F.FInt) singleOne !! depth
    _ <- evaluate (force (singleEnvironment, term))
    let result = C.checkSortExpr Nothing F.dummySpan singleEnvironment term
    bytes <- allocationBytes result
    result @?= Just F.FInt
    pure bytes
