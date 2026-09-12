{-# LANGUAGE OverloadedStrings #-}

module PolyValueTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad (void)
import Control.Monad.State (evalStateT, gets, runState)
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.HashMap.Strict as M
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Store as Store
import qualified Language.Fixpoint.Smt.Interface as SMT
import Language.Fixpoint.Smt.Serialize ()
import qualified Language.Fixpoint.Smt.Theories as Thy
import Language.Fixpoint.Smt.Types (Command (..), SMTLIB2, runSmt2)
import Language.Fixpoint.Types
import Language.Fixpoint.Types.Config (ElabFlags (..), SMTSolver (Z3), defConfig)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Test.Tasty
import Test.Tasty.HUnit

scheme, integers, tokens, generic :: Sort
scheme = FAbs 0 (arraySort (FVar 0) boolSort)
integers = arraySort intSort boolSort
tokens = arraySort token boolSort
generic = arraySort (FObj "a") boolSort

token :: Sort
token = fAppTC (symbolFTycon (dummyLoc "Token")) []

environment :: SymEnv
environment =
    mempty
        { seSort = fromListSEnv [("family", scheme), ("other", scheme)]
        , seData =
            fromListSEnv
                [
                    ( "Token"
                    , DDecl
                        (symbolFTycon (dummyLoc "Token"))
                        0
                        [DCtor (dummyLoc "First") [], DCtor (dummyLoc "Second") []]
                    )
                ]
        }

render :: (SMTLIB2 a) => SymEnv -> a -> (String, SymEnv)
render env expression = (BS.unpack (toLazyByteString output), final)
  where
    (output, final) = runState (runSmt2 expression) env

value :: Symbol -> Sort -> Expr
value name = ECst (EVar name)

rejects :: (SMTLIB2 a) => String -> a -> Assertion
rejects message expression = do
    result <-
        try (evaluate (length (fst (render environment expression)))) ::
            IO (Either SomeException Int)
    case result of
        Left exception -> assertBool (show exception) (message `isInfixOf` show exception)
        Right _ -> assertFailure "unsupported family expression was serialized"

rejectsFixture :: FilePath -> [String] -> Assertion
rejectsFixture fixture diagnostics = do
    (code, output, errors) <- readProcessWithExitCode "fixpoint" [fixture] ""
    let diagnostic = output ++ errors
    assertBool "ill-sorted fixture unexpectedly succeeded" (code /= ExitSuccess)
    mapM_ (\expected -> assertBool diagnostic (expected `isInfixOf` diagnostic)) diagnostics

tests :: TestTree
tests =
    testGroup
        "polymorphic nullary value families"
        [ testCase "same name and result sort share the same value" $ do
            let (first, env) = render environment (value "family" tokens)
            fst (render env (value "family" tokens)) @?= first
            M.size (seApplsCur env) @?= 1
        , testCase "different family names are not conflated" $ do
            let (first, env) = render environment (value "family" tokens)
            assertBool
                "distinct family names serialized identically"
                (first /= fst (render env (value "other" tokens)))
        , testCase "different actual result sorts get different applications" $ do
            let (_, env) = render environment (value "family" tokens)
                (_, final) = render env (value "family" integers)
            M.size (seApplsCur final) @?= 2
            assertBool
                "Token array result sort was erased"
                ((SInt, SArray (SData (symbolFTycon (dummyLoc "Token")) []) SBool) `M.member` seApplsCur final)
        , testCase "existing generic-sort erasure shares the concrete SMT instance" $ do
            let (first, env) = render environment (value "family" generic)
            fst (render env (value "family" integers)) @?= first
            M.size (seApplsCur env) @?= 1
        , testCase "raw whole-family EVar rejects" $
            rejects "uninstantiated polymorphic value family" (EVar "family" :: Expr)
        , testCase "whole-family value query rejects rather than exposing its tag" $
            rejects "uninstantiated polymorphic value family" (GetValue ["family"])
        , testCase "residual FAbs target rejects" $
            rejects "uninstantiated polymorphic value family" (value "family" scheme)
        , testCase "unstructured Int and function instances remain distinct" $ do
            let env = insertSymEnv "undef" (FAbs 0 (FVar 0)) environment
                (integer, first) = render env (value "undef" intSort)
                (function, second) = render first (value "undef" (FFunc intSort boolSort))
            assertBool "function instance identified with Int instance" (integer /= function)
            Map.size (seValueInsts second) @?= 2
        , testCase "recursive function sort normal forms share an instance" $ do
            let direct = arraySort (FFunc intSort boolSort) boolSort
                elaborated = arraySort (FApp (FApp funcSort intSort) boolSort) boolSort
                (first, env) = render environment (value "family" direct)
            fst (render env (value "family" elaborated)) @?= first
            normalizeValueInstance direct @?= normalizeValueInstance elaborated
        , testCase "nested function and Int instances remain distinct" $ do
            let (first, env) = render environment (value "family" integers)
                (second, final) = render env (value "family" (arraySort (FFunc intSort intSort) boolSort))
            assertBool "nested function structure erased" (first /= second)
            Map.size (seValueInsts final) @?= 2
        , testCase "nested higher-rank instance rejects" $
            rejects
                "higher-rank polymorphic value instance"
                (value "family" (arraySort (FFunc (FAbs 0 (FVar 0)) intSort) boolSort))
        , testCase "distinct nominal string-like types retain identity" $ do
            let firstType = FTC (mappendFTC (symbolFTycon (dummyLoc "TextLikeA")) strFTyCon)
                secondType = FTC (mappendFTC (symbolFTycon (dummyLoc "TextLikeB")) strFTyCon)
            assertBool
                "test sorts must both have string representation"
                (isString firstType && isString secondType)
            assertBool
                "string representation erased nominal instance identity"
                (normalizeValueInstance firstType /= normalizeValueInstance secondType)
        , testCase "unused phantom declarations do not select an instance" $ do
            let phantom = FAbs 0 (FAbs 1 (FVar 1))
                env = insertSymEnv "phantom" phantom environment
            polyValueSort env "phantom" @?= Just phantom
            bracket
                (SMT.makeContextWithSEnv defConfig "unused-phantom" env mempty)
                SMT.cleanupContext
                $ \context -> do
                    (satisfiable, contradictory) <- flip evalStateT context $ do
                        first <- SMT.smtCheckUnsat
                        SMT.smtAssert PFalse
                        second <- SMT.smtCheckUnsat
                        pure (first, second)
                    satisfiable @?= False
                    contradictory @?= True
        , testCase "phantom quantification rejects at an actual instance" $ do
            let env = insertSymEnv "phantom" (FAbs 0 intSort) environment
            result <-
                try (evaluate (length (fst (render env (value "phantom" intSort))))) ::
                    IO (Either SomeException Int)
            case result of
                Left exception ->
                    assertBool
                        (show exception)
                        ("phantom type parameter" `isInfixOf` show exception)
                Right _ -> assertFailure "phantom family instance was silently chosen"
        , testCase "former undef00 fixture rejects with the supported-boundary diagnostic" $ do
            (code, output, errors) <- readProcessWithExitCode "fixpoint" ["tests/crash/undef00.fq"] ""
            assertBool "unsupported phantom fixture unexpectedly succeeded" (code /= ExitSuccess)
            assertBool (output ++ errors) ("phantom type parameter" `isInfixOf` (output ++ errors))
        , testCase "selected GADT branch retains strict sort checking" $
            rejectsFixture
                "tests/crash/polyvalue-ple-reachable-sort.fq"
                ["EvalApp guard", "Cannot unify int with bool"]
        , testCase "requested pending equations pass through resSInfo sort checking" $
            rejectsFixture
                "tests/crash/polyvalue-ple-pending-sort.fq"
                ["elaborate PLE1 1", "Cannot unify int with bool"]
        , testCase "ordinary polymorphic functions remain defunctionalized functions" $ do
            let env = insertSymEnv "function" (FAbs 0 (FFunc (FVar 0) (FVar 0))) environment
            polyValueSort env "function" @?= Nothing
        , testCase "authoritative native theory symbols do not become family tags" $ do
            let theory = Thy.theorySymbols Z3
                env =
                    environment
                        { seSort = insertSEnv Thy.setEmpty scheme (seSort environment)
                        , seTheory = theory
                        }
            assertBool
                "missing native empty-set theory classification"
                ( case symEnvTheory Thy.setEmpty env of
                    Just entry -> tsInterp entry == Theory
                    Nothing -> False
                )
            polyValueSort env Thy.setEmpty @?= Nothing
        , testCase "true nullary datatype constructors keep as syntax" $ do
            let constructor = symbolFTycon (dummyLoc "List")
                datatype = DDecl constructor 1 [DCtor (dummyLoc "Nil") []]
                listScheme = FAbs 0 (fAppTC constructor [FVar 0])
                env =
                    environment
                        { seSort = insertSEnv "Nil" listScheme (seSort environment)
                        , seTheory = Thy.theorySymbols [datatype]
                        , seData = insertSEnv "List" datatype (seData environment)
                        }
            polyValueSort env "Nil" @?= Nothing
            assertBool
                "lost constructor as syntax"
                ("(as Nil " `isInfixOf` fst (render env (value "Nil" (fAppTC constructor [token]))))
        , testCase "polymorphic quantifier rejects explicitly" $
            rejects
                "quantified polymorphic value families"
                (PAll [("local", scheme)] (PAtom Eq (value "local" integers) (value "local" integers)) :: Expr)
        , testCase "polymorphic lambda binder rejects explicitly" $
            rejects
                "quantified polymorphic value families"
                (ELam ("local", scheme) (ECst PTrue boolSort) :: Expr)
        , testGroup
            "monomorphic binders shadow global family schemes"
            [ testCase name $ do
                let (output, final) = render environment expression
                assertBool output (not ("apply" `isInfixOf` output))
                seSort final @?= seSort environment
            | let body = PAtom Eq (value "family" intSort) (value "family" intSort)
            , (name, expression) <-
                [ ("forall", PAll [("family", intSort)] body)
                , ("exists", PExist [("family", intSort)] body)
                , ("let", ELet "family" (ECon (I 0)) body)
                , ("lambda", ELam ("family", intSort) (ECst body boolSort))
                ]
            ]
        , testCase "define-fun arguments shadow global family schemes" $ do
            let body = PAtom Eq (value "family" integers) (value "family" integers)
                command = DefineFunc "test" [("family", SArray SInt SBool)] SBool body
                (output, final) = render environment command
            assertBool output (not ("apply" `isInfixOf` output))
            seSort final @?= seSort environment
        , testCase "sort nursery survives shadow scopes and is re-created after pop" $ do
            let expression =
                    PAll
                        [("local", intSort)]
                        (PAtom Eq (value "family" tokens) (value "family" tokens))
                (_, created) = render environment expression
                committed =
                    created
                        { seAppls = mergeTopAppls (seApplsCur created) (seAppls created)
                        , seApplsCur = M.empty
                        }
                pushed = committed{seAppls = pushAppls (seAppls committed)}
                (_, local) = render pushed (value "family" integers)
                popped =
                    local
                        { seAppls = popAppls (seAppls local)
                        , seApplsCur = M.empty
                        , seIx = seIx committed
                        }
                (_, recreated) = render popped (value "family" integers)
            M.size (seApplsCur created) @?= 1
            M.size (seApplsCur recreated) @?= 1
            seValueInsts recreated @?= seValueInsts local
            seValueIx recreated @?= seValueIx local
        , testGroup
            "logical instance registry merging"
            [ testCase "compatible subset preserves live IDs" $ do
                let (_, first) = render environment (value "family" integers)
                    (_, second) = render first (value "family" tokens)
                    combined = first <> second
                seValueInsts combined @?= seValueInsts second
                seValueIx combined @?= seValueIx second
            , testCase "independent conflicting allocations reject" $ do
                let (_, first) = render environment (value "family" integers)
                    (_, second) = render environment (value "family" tokens)
                outcome <-
                    try (evaluate (Map.size (seValueInsts (first <> second)))) ::
                        IO (Either SomeException Int)
                case outcome of
                    Left exception ->
                        assertBool
                            (show exception)
                            ("incompatible polymorphic value instance registries" `isInfixOf` show exception)
                    Right _ -> assertFailure "different logical sorts inherited the same live ID"
            , testCase "coercing environment preserves live registry" $ do
                let (_, original) = render environment (value "family" integers)
                    coerced = coerceEnv (ElabFlags True False) original
                seValueInsts coerced @?= seValueInsts original
                seValueIx coerced @?= seValueIx original
            , testCase "same logical key with different live IDs rejects" $ do
                let (_, first) = render environment (value "family" integers)
                    (_, tokenFirst) = render environment (value "family" tokens)
                    (_, second) = render tokenFirst (value "family" integers)
                outcome <- try (evaluate (Map.size (seValueInsts (first <> second)))) :: IO (Either SomeException Int)
                case outcome of
                    Left exception -> assertBool (show exception) ("incompatible polymorphic value instance registries" `isInfixOf` show exception)
                    Right _ -> assertFailure "same logical key had its live ID renumbered"
            , testCase "NFData and Store retain the populated registry" $ do
                let (_, first) = render environment (value "family" integers)
                    (_, original) = render first (value "family" tokens)
                strict <- evaluate (force original)
                case Store.decode (Store.encode strict) of
                    Left failure -> assertFailure (show failure)
                    Right restored -> do
                        seValueInsts restored @?= seValueInsts original
                        seValueIx restored @?= seValueIx original
                        fst (render restored (value "family" tokens)) @?= fst (render original (value "family" tokens))
            ]
        , testCase "real nested solver scopes preserve IDs and redeclare applications"
            $ bracket
                (SMT.makeContextWithSEnv defConfig "polyvalue-scopes" environment mempty)
                SMT.cleanupContext
            $ \context -> do
                let relation operator sort = PAtom operator (value "family" sort) (value "other" sort)
                    functionArrays = arraySort (FFunc intSort intSort) boolSort
                    registry = gets (seValueInsts . SMT.ctxSymEnv)
                (verdicts, inside, after, fresh) <- flip evalStateT context $ do
                    SMT.smtAssert (relation Ne tokens)
                    initial <- SMT.smtCheckUnsat
                    (nestedVerdicts, allocated) <- SMT.smtBracket "outer" $ do
                        SMT.smtAssert (relation Ne integers)
                        beforeInner <- SMT.smtCheckUnsat
                        inner <- SMT.smtBracket "inner" $ do
                            SMT.smtAssert (relation Eq integers)
                            SMT.smtCheckUnsat
                        afterInner <- SMT.smtCheckUnsat
                        current <- registry
                        pure ([beforeInner, inner, afterInner], current)
                    afterOuter <- SMT.smtCheckUnsat
                    SMT.smtAssert (relation Ne integers)
                    recreated <- registry
                    SMT.smtAssert (relation Ne functionArrays)
                    finalRegistry <- registry
                    distinct <- SMT.smtCheckUnsat
                    SMT.smtAssert (relation Eq tokens)
                    contradictory <- SMT.smtCheckUnsat
                    pure (initial : nestedVerdicts ++ [afterOuter, distinct, contradictory], allocated, recreated, finalRegistry)
                verdicts @?= [False, False, True, False, False, False, True]
                case (normalizeValueInstance integers, normalizeValueInstance functionArrays) of
                    (Just integerKey, Just functionKey) ->
                        case (Map.lookup integerKey inside, Map.lookup integerKey after, Map.lookup integerKey fresh, Map.lookup functionKey fresh) of
                            (Just originalId, Just restoredId, Just retainedId, Just functionId) -> do
                                restoredId @?= originalId
                                retainedId @?= originalId
                                assertBool "post-pop logical instance reused a live ID" (functionId /= originalId)
                            missing -> assertFailure ("missing normalized registry instance: " ++ show missing)
                    _ -> assertFailure "ordinary instance normalization rejected"
        , testGroup
            "solver declarations precede first family use"
            [ testCase name
                $ bracket
                    (SMT.makeContextWithSEnv defConfig "polyvalue-tests" environment mempty)
                    SMT.cleanupContext
                $ \context -> do
                    let left = value "family" tokens
                        right = value "other" tokens
                    (satisfiable, contradictory) <- flip evalStateT context $ do
                        firstAssertion (PAtom Ne left right)
                        first <- SMT.smtCheckUnsat
                        SMT.smtAssert (PAtom Eq left right)
                        second <- SMT.smtCheckUnsat
                        pure (first, second)
                    satisfiable @?= False
                    contradictory @?= True
            | (name, firstAssertion) <-
                [ ("ordinary assert", SMT.smtAssert)
                , ("axiom", SMT.smtAssertAxiom . noTrigger)
                ,
                    ( "distinct"
                    , \_ ->
                        SMT.smtDistinct
                            [value "family" tokens, value "other" tokens]
                    )
                , ("direct command", void . SMT.command . Assert Nothing)
                ,
                    ( "define-fun body"
                    , \_ -> do
                        SMT.smtDefineFunc "definedValue" [] tokens (value "family" tokens)
                        SMT.smtAssert (PAtom Ne (EVar "definedValue") (value "other" tokens))
                    )
                ]
            ]
        ]
