{-# LANGUAGE OverloadedStrings #-}

module PolyFamilyTests (tests) where

import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad (void)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (evalStateT, gets, runState)
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.HashMap.Strict as M
import Data.List (isInfixOf, nub)
import qualified Language.Fixpoint.Smt.Interface as SMT
import Language.Fixpoint.Smt.Serialize ()
import Language.Fixpoint.Smt.Types (Command (Assert, GetValue), SMTLIB2, runSmt2)
import qualified Language.Fixpoint.SortCheck as So
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

scheme :: F.Sort
scheme = F.FAbs 0 (F.FVar 0)

environment :: F.SymEnv
environment = F.emptySymEnv{F.seSort = F.fromListSEnv [("family", scheme), ("other", scheme)]}

render :: (SMTLIB2 a) => F.SymEnv -> a -> (String, F.SymEnv)
render env expression = (BS.unpack (toLazyByteString builder), final)
  where
    (builder, final) = runState (runSmt2 expression) env

selected :: F.Symbol -> F.Sort -> F.Expr
selected name = F.ECst (F.EVar name)

rejects :: (SMTLIB2 a) => String -> F.SymEnv -> a -> Assertion
rejects expected env expression = do
    result <- try (evaluate (length (fst (render env expression)))) :: IO (Either SomeException Int)
    case result of
        Left exception -> assertBool (show exception) (expected `isInfixOf` show exception)
        Right _ -> assertFailure "unsupported polymorphic family was serialized"

checkTruth :: F.Expr -> Bool -> IO ()
checkTruth expression expected =
    bracket
        (SMT.makeContextWithSEnv C.defConfig "poly-family-truth" environment mempty)
        SMT.cleanupContext
        $ \context -> do
            actual <- flip evalStateT context $ SMT.smtAssert expression >> SMT.smtCheckUnsat
            actual @?= expected

tests :: TestTree
tests =
    testGroup
        "polymorphic value families"
        [ testCase "same logical instance has one scoped value" $ do
            let (first, state) = render environment (selected "family" F.intSort)
            fst (render state (selected "family" F.intSort)) @?= first
            assertBool "different families share a value" (fst (render state (selected "other" F.intSort)) /= first)
        , testCase "function and integer instances remain distinct before SMT erasure" $ do
            let (integer, state) = render environment (selected "family" F.intSort)
                (function, _) = render state (selected "family" (F.FFunc F.intSort F.boolSort))
            assertBool "logical function instance was erased" (integer /= function)
        , testCase "distinct nominal string-like sorts retain family identity" $ do
            let nominal name = F.FTC (F.mappendFTC (F.symbolFTycon (F.dummyLoc name)) F.strFTyCon)
                firstSort = nominal "TextLikeA"
                secondSort = nominal "TextLikeB"
                (first, state) = render environment (selected "family" firstSort)
                (second, final) = render state (selected "family" secondSort)
            assertBool "test sorts must share a string SMT carrier" (F.isString firstSort && F.isString secondSort)
            assertBool "distinct nominal instances shared a value" (first /= second)
            M.size (F.valueDeclarations (F.seDeclarationsCur final)) @?= 2
        , testCase "canonical String and [Char] select one family instance, including nested sorts" $ do
            let stringList = F.FApp (F.FTC F.listFTyCon) F.charSort
                (string, first) = render environment (selected "family" F.strSort)
                (list, second) = render first (selected "family" stringList)
                (functionString, third) = render second (selected "family" (F.FFunc F.strSort F.boolSort))
                (functionList, final) = render third (selected "family" (F.FFunc stringList F.boolSort))
            string @?= list
            functionString @?= functionList
            M.size (F.valueDeclarations (F.seDeclarationsCur final)) @?= 2
        , testCase "nominal family instances retain their native string carrier" $ do
            let nominal = F.FTC (F.mappendFTC (F.symbolFTycon (F.dummyLoc "TextLikeA")) F.strFTyCon)
                env = F.insertSymEnv "actual" nominal environment
                parameter = So.ElabParam (C.solverFlags C.defConfig) "nominal family carrier" env
                relation operator = So.elaborate parameter (F.PAtom operator (F.EVar "actual") (selected "family" nominal))
            bracket
                (SMT.makeContextWithSEnv C.defConfig "nominal family carrier" env mempty)
                SMT.cleanupContext
                $ \context -> do
                    verdicts <- flip evalStateT context $ do
                        SMT.smtAssert (relation F.Eq)
                        inhabited <- SMT.smtCheckUnsat
                        SMT.smtAssert (relation F.Ne)
                        contradictory <- SMT.smtCheckUnsat
                        pure (inhabited, contradictory)
                    verdicts @?= (False, True)
        , testCase "source locations do not split nominal family identity" $ do
            let nominal source = F.FTC (F.mappendFTC (F.symbolFTycon (F.locAt source "TextLikeA")) F.strFTyCon)
                (first, state) = render environment (selected "family" (nominal "first"))
                (second, final) = render state (selected "family" (nominal "second"))
            first @?= second
            M.size (F.valueDeclarations (F.seDeclarationsCur final)) @?= 1
        , testCase "sequential instances preserve an emitted name" $ do
            let (_, first) = render environment (selected "family" F.intSort)
                (_, second) = render first (selected "family" F.boolSort)
                (again, final) = render second (selected "family" F.intSort)
                (original, _) = render environment (selected "family" F.intSort)
            again @?= original
            F.valueDeclarations (F.seDeclarationsCur final) @?= F.valueDeclarations (F.seDeclarationsCur second)
        , testCase "independent contexts keep their own instance identities" $ do
            let (_, first) = render environment (selected "family" F.intSort)
                (_, second) = render environment (selected "family" F.boolSort)
            M.keys (F.valueDeclarations (F.seDeclarationsCur first)) @?= [("family", F.intSort)]
            M.keys (F.valueDeclarations (F.seDeclarationsCur second)) @?= [("family", F.boolSort)]
        , testCase "whole family requires a selected result sort" $
            rejects "uninstantiated polymorphic value family" environment (F.EVar "family" :: F.Expr)
        , testCase "whole-family value query cannot expose an instance tag" $
            rejects "uninstantiated polymorphic value family" environment (GetValue ["family"])
        , testCase "phantom parameter cannot select an instance" $
            rejects
                "phantom type parameter"
                environment{F.seSort = F.insertSEnv "phantom" (F.FAbs 0 F.intSort) (F.seSort environment)}
                (selected "phantom" F.intSort)
        , testCase "nested higher-rank result is unsupported" $
            rejects
                "higher-rank polymorphic value instance"
                environment
                (selected "family" (F.FFunc (F.FAbs 1 (F.FVar 1)) F.boolSort))
        , testCase "unused family binder disappears without changing truth" $ do
            let quantified = F.PExist [("family", scheme)] F.PFalse :: F.Expr
            fst (render environment quantified) @?= fst (render environment (F.PFalse :: F.Expr))
            checkTruth quantified True
        , testCase "unused universal binder preserves true" $ do
            let quantified = F.PAll [("family", scheme)] F.PTrue :: F.Expr
            fst (render environment quantified) @?= fst (render environment (F.PTrue :: F.Expr))
            checkTruth quantified False
        , testCase "used quantified family is rejected" $
            rejects
                "quantified polymorphic value families"
                environment
                (F.PAll [("family", scheme)] (F.PAtom F.Eq (selected "family" F.intSort) (selected "family" F.intSort)))
        , testCase "type application cannot hide a family use" $
            rejects
                "quantified polymorphic value families"
                environment
                (F.PExist [("family", scheme)] (F.ETApp (F.PAtom F.Eq (selected "family" F.intSort) (selected "family" F.intSort)) F.intSort))
        , testCase "nested monomorphic binder shadows a family" $ do
            let inner :: F.Expr
                inner = F.PAll [("family", F.intSort)] (F.PAtom F.Eq (F.EVar "family") (F.EVar "family"))
            fst (render environment (F.PExist [("family", scheme)] inner)) @?= fst (render environment inner)
        , testCase "nested shadow does not hide a sibling family use" $
            rejects
                "quantified polymorphic value families"
                environment
                (F.PExist [("family", scheme)] (F.PAnd [F.PAll [("family", F.intSort)] F.PTrue, F.PAtom F.Eq (selected "family" F.intSort) (selected "family" F.intSort)]))
        , testCase "let binder shadows a family only in its body" $ do
            let inner :: F.Expr
                inner = F.ELet "family" (F.ECon (F.I 0)) (F.PAtom F.Eq (F.EVar "family") (F.EVar "family"))
            fst (render environment (F.PExist [("family", scheme)] inner)) @?= fst (render environment inner)
        , testCase "let initializer still uses the outer family" $
            rejects
                "quantified polymorphic value families"
                environment
                (F.PExist [("family", scheme)] (F.ELet "family" (selected "family" F.intSort) F.PTrue))
        , testCase "type abstraction cannot hide a family use" $
            rejects
                "quantified polymorphic value families"
                environment
                (F.PExist [("family", scheme)] (F.ETAbs (F.PAtom F.Eq (selected "family" F.intSort) (selected "family" F.intSort)) "family"))
        , testCase "KVar substitution cannot hide a family use" $
            rejects
                "quantified polymorphic value families"
                environment
                (F.PExist [("family", scheme)] (F.PKVar (F.KV "k") mempty (F.toKVarSubst (M.singleton "argument" (selected "family" F.intSort)))))
        , testCase "triggered used family is rejected" $
            rejects
                "quantified polymorphic value families"
                environment
                (F.TR (F.Patterns [[selected "family" F.intSort]]) (F.PAll [("family", scheme)] (F.PAtom F.Eq (selected "family" F.intSort) (selected "family" F.intSort))))
        , testCase "triggered unused family retains the body" $ do
            let body = F.PAtom F.Eq (F.ECon (F.I 0)) (F.ECon (F.I 0)) :: F.Expr
            fst (render environment (F.TR (F.Patterns [[F.ECon (F.I 0)]]) (F.PAll [("family", scheme)] body))) @?= fst (render environment body)
        , testCase "triggered unused existential retains solver truth"
            $ bracket
                (SMT.makeContextWithSEnv C.defConfig "poly-family-triggered-existential" environment mempty)
                SMT.cleanupContext
            $ \context -> do
                actual <- flip evalStateT context $ do
                    SMT.smtAssertAxiom (F.TR (F.Patterns [[F.PFalse]]) (F.PExist [("family", scheme)] F.PFalse))
                    SMT.smtCheckUnsat
                actual @?= True
        , testGroup
            "ordinary binders shadow global families in the solver"
            [ testCase name
                $ bracket
                    (SMT.makeContextWithSEnv C.defConfig "poly-family-shadow" environment mempty)
                    SMT.cleanupContext
                $ \context -> do
                    let applied = F.EApp (F.EVar "f")
                        axiom = F.PAll binders (F.PAtom F.Eq (applied (selected "family" F.intSort)) (selected "family" F.intSort))
                    verdicts <- flip evalStateT context $ do
                        SMT.smtDecl "f" (F.FFunc F.intSort F.intSort)
                        if triggered
                            then SMT.smtAssertAxiom (F.TR (F.Patterns [[applied (selected "family" F.intSort)]]) axiom)
                            else SMT.smtAssert axiom
                        before <- SMT.smtCheckUnsat
                        SMT.smtAssert (F.PAtom F.Ne (applied (F.ECon (F.I 1))) (F.ECon (F.I 1)))
                        after <- SMT.smtCheckUnsat
                        pure (before, after)
                    verdicts @?= (False, True)
            | (name, binders, triggered) <-
                [ ("plain", [("family", F.intSort)], False)
                , ("triggered", [("family", F.intSort)], True)
                , ("triggered after unused family removal", [("unused", scheme), ("family", F.intSort)], True)
                ]
            ]
        , testGroup
            "first use declares a selected family value"
            [ testCase name
                $ bracket
                    (SMT.makeContextWithSEnv C.defConfig "poly-family-declarations" environment mempty)
                    SMT.cleanupContext
                $ \context -> do
                    let left = selected "family" F.intSort
                        right = selected "other" F.intSort
                        unequal = F.PAtom F.Ne left right
                    (satisfiable, contradictory) <- flip evalStateT context $ do
                        firstUse unequal
                        first <- SMT.smtCheckUnsat
                        SMT.smtAssert (F.PAtom F.Eq left right)
                        second <- SMT.smtCheckUnsat
                        pure (first, second)
                    satisfiable @?= False
                    contradictory @?= True
            | (name, firstUse) <-
                [ ("assert", SMT.smtAssert)
                , ("axiom", SMT.smtAssertAxiom . F.noTrigger)
                , ("distinct", \_ -> SMT.smtDistinct [selected "family" F.intSort, selected "other" F.intSort])
                , ("direct command", void . SMT.command . Assert Nothing)
                ,
                    ( "define-fun body"
                    , \_ -> do
                        SMT.smtDefineFunc "definedValue" [] F.intSort (selected "family" F.intSort)
                        SMT.smtAssert (F.PAtom F.Ne (F.EVar "definedValue") (selected "other" F.intSort))
                    )
                ]
            ]
        , testCase "nested solver scopes retain live family identities"
            $ bracket
                (SMT.makeContextWithSEnv C.defConfig "poly-family-scopes" scopedEnvironment mempty)
                SMT.cleanupContext
            $ \context -> do
                let relation operator sort = F.PAtom operator (selected "family" sort) (selected "other" sort)
                    registry = do
                        current <- gets SMT.ctxSymEnv
                        let scopes = F.seDeclarationsCur current : F.seDeclarations current
                            keys = concatMap M.keys scopes
                        liftIO (assertBool "a live declaration key occurs in multiple frames" (length keys == length (nub keys)))
                        liftIO (assertBool "a live name reaches the fresh frontier" (all (< F.seIx current) (concatMap M.elems scopes)))
                        pure (M.unions (map F.valueDeclarations scopes))
                    functionSort = F.FFunc F.intSort F.boolSort
                    native = F.ECst (F.EVar "nativeNot") (F.FFunc F.boolSort F.boolSort)
                    nativeIdentity = F.PAtom F.Eq native native
                (verdicts, inside, recreated, final) <- flip evalStateT context $ do
                    SMT.smtAssert (relation F.Ne F.intSort)
                    initial <- SMT.smtCheckUnsat
                    frontier <- gets (F.seIx . SMT.ctxSymEnv)
                    (nestedVerdicts, inOuter) <- SMT.smtBracket "outer" $ do
                        SMT.smtAssert nativeIdentity
                        SMT.smtAssert (relation F.Ne F.boolSort)
                        beforeInner <- SMT.smtCheckUnsat
                        inner <- SMT.smtBracket "inner" $ do
                            SMT.smtAssert (relation F.Eq F.boolSort)
                            SMT.smtCheckUnsat
                        afterInner <- SMT.smtCheckUnsat
                        current <- registry
                        pure ([beforeInner, inner, afterInner], current)
                    afterOuter <- SMT.smtCheckUnsat
                    restored <- gets (F.seIx . SMT.ctxSymEnv)
                    liftIO (restored @?= frontier)
                    afterPop <- registry
                    liftIO (assertBool "native instance outlived its solver scope" (not (M.member ("nativeNot", F.FFunc F.boolSort F.boolSort) afterPop)))
                    SMT.smtAssert nativeIdentity
                    SMT.smtAssert (relation F.Ne F.boolSort)
                    afterRecreation <- registry
                    SMT.smtAssert (relation F.Ne functionSort)
                    afterFunction <- registry
                    distinct <- SMT.smtCheckUnsat
                    SMT.smtAssert (relation F.Eq F.intSort)
                    contradictory <- SMT.smtCheckUnsat
                    pure (initial : nestedVerdicts ++ [afterOuter, distinct, contradictory], inOuter, afterRecreation, afterFunction)
                verdicts @?= [False, False, True, False, False, False, True]
                case (M.lookup ("family", F.boolSort) inside, M.lookup ("family", F.boolSort) recreated) of
                    (Just original, Just restored) -> restored @?= original
                    missing -> assertFailure ("missing selected family instance: " ++ show missing)
                let liveNames = M.elems final
                assertBool "distinct live instances share an SMT name" (length liveNames == length (nub liveNames))
        ]
  where
    scopedEnvironment = F.insertSymEnv "nativeNot" (F.FFunc F.boolSort F.boolSort) environment{F.seTheory = F.fromListSEnv [("nativeNot", F.Thy "nativeNot" "not" (F.FFunc F.boolSort F.boolSort) F.Theory)]}
