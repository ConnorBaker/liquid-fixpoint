{-# LANGUAGE OverloadedStrings #-}

module QuantifiedFamilyTests (tests) where

import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad.State (evalStateT, runState)
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.HashMap.Strict as M
import Data.List (isInfixOf)
import qualified Language.Fixpoint.Smt.Interface as SMT
import Language.Fixpoint.Smt.Serialize ()
import Language.Fixpoint.Smt.Types (SMTLIB2, runSmt2)
import Language.Fixpoint.Types
import Language.Fixpoint.Types.Config (defConfig)
import Test.Tasty
import Test.Tasty.HUnit

scheme :: Sort
scheme = FAbs 0 (FVar 0)

environment :: SymEnv
environment = mempty{seSort = fromListSEnv [("family", scheme)]}

render :: (SMTLIB2 a) => a -> (String, SymEnv)
render expression = (BS.unpack (toLazyByteString output), final)
  where
    (output, final) = runState (runSmt2 expression) environment

integer :: Symbol -> Expr
integer name = ECst (EVar name) intSort

identity :: Symbol -> Expr
identity name = PAtom Eq (integer name) (integer name)

rejectsFamily :: (SMTLIB2 a) => a -> Assertion
rejectsFamily expression = do
    outcome <- try (evaluate (length (fst (render expression)))) :: IO (Either SomeException Int)
    case outcome of
        Left exception ->
            assertBool
                (show exception)
                ("SMTLIB2: quantified polymorphic value families are not supported" `isInfixOf` show exception)
        Right _ -> assertFailure "used quantified family was silently serialized"

preserves :: Expr -> Expr -> Assertion
preserves original simplified = do
    fst (render original) @?= fst (render simplified)
    seSort (snd (render original)) @?= seSort environment

checkUnsat :: Expr -> IO Bool
checkUnsat expression =
    bracket
        (SMT.makeContextWithSEnv defConfig "quantified-family-truth" environment mempty)
        SMT.cleanupContext
        $ \context -> flip evalStateT context $ do
            SMT.smtAssert expression
            SMT.smtCheckUnsat

checkAxiomUnsat :: Triggered Expr -> IO Bool
checkAxiomUnsat expression =
    bracket
        (SMT.makeContextWithSEnv defConfig "quantified-family-axiom-truth" environment mempty)
        SMT.cleanupContext
        $ \context -> flip evalStateT context $ do
            SMT.smtAssertAxiom expression
            SMT.smtCheckUnsat

checkTriggeredIdentity :: [(Symbol, Sort)] -> Bool -> IO (Bool, Bool)
checkTriggeredIdentity binders triggered =
    bracket
        (SMT.makeContextWithSEnv defConfig "quantified-family-trigger" environment mempty)
        SMT.cleanupContext
        $ \context -> flip evalStateT context $ do
            SMT.smtFuncDecl "f" ([SInt], SInt)
            if triggered
                then SMT.smtAssertAxiom (defaultTrigger axiom)
                else SMT.smtAssert axiom
            before <- SMT.smtCheckUnsat
            SMT.smtAssert (PAtom Ne (apply (ECon (I 1))) (ECon (I 1)))
            after <- SMT.smtCheckUnsat
            pure (before, after)
  where
    apply = EApp (EVar "f")
    axiom = PAll binders (PAtom Eq (apply (integer "family")) (integer "family"))

tests :: TestTree
tests =
    testGroup
        "unused quantified families and lexical scope"
        [ testGroup
            "dropping an unused family preserves the body"
            [ testCase (quantifierName ++ " " ++ truthName) $ do
                let expression = quantifier [("family", scheme)] body
                preserves expression body
                actual <- checkUnsat expression
                actual @?= expectedUnsat
            | (quantifierName, quantifier) <- [("exists", PExist), ("forall", PAll)]
            , (truthName, body, expectedUnsat) <- [("true", PTrue, False), ("false", PFalse, True)]
            ]
        , testGroup
            "used family binders still reject"
            [ testCase quantifierName $ rejectsFamily (quantifier [("family", scheme)] (identity "family"))
            | (quantifierName, quantifier) <- [("exists", PExist), ("forall", PAll)]
            ]
        , testCase "triggered used family still rejects" $
            rejectsFamily (defaultTrigger (PAll [("family", scheme)] (identity "family")))
        , testCase "unused lambda family still rejects" $
            rejectsFamily (ELam ("family", scheme) (ECst PTrue boolSort) :: Expr)
        , testCase "remaining monomorphic binder is preserved" $ do
            let body = identity "ordinary"
            preserves
                (PAll [("family", scheme), ("ordinary", intSort)] body)
                (PAll [("ordinary", intSort)] body)
        , testCase "nested quantifier shadows the outer family" $ do
            let inner = PAll [("family", intSort)] (identity "family")
            preserves (PExist [("family", scheme)] inner) inner
        , testCase "nested shadow does not hide a sibling outer use" $
            rejectsFamily
                ( PExist
                    [("family", scheme)]
                    (PAnd [PAll [("family", intSort)] (identity "family"), identity "family"])
                )
        , testCase "let binder shadows family only in its body" $ do
            let inner = ELet "family" (ECon (I 0)) (identity "family")
            preserves (PExist [("family", scheme)] inner) inner
        , testCase "let initializer still uses the outer family" $
            rejectsFamily
                (PExist [("family", scheme)] (ELet "family" (integer "family") (identity "family")))
        , testGroup
            "unsupported type syntax cannot hide a family use"
            [ testCase name $ rejectsFamily (PExist [("family", scheme)] body)
            | (name, body) <-
                [ ("ETApp", ETApp (identity "family") intSort)
                , ("ETAbs", ETAbs (identity "family") "a")
                , ("same-spelling type binder", ETAbs (identity "family") "family")
                ]
            ]
        , testCase "KVar substitution cannot hide a family use" $
            rejectsFamily
                ( PExist
                    [("family", scheme)]
                    (PKVar (KV "k") mempty (toKVarSubst (M.singleton "argument" (integer "family"))))
                )
        , testCase "pruned triggered quantifier retains its body" $ do
            let body = PAtom Eq (ECon (I 0)) (ECon (I 0)) :: Expr
            fst (render (defaultTrigger (PAll [("family", scheme)] body))) @?= fst (render body)
        , testCase "pruned triggered existential retains false" $ do
            let axiom = defaultTrigger (PExist [("family", scheme)] PFalse :: Expr)
            fst (render axiom) @?= fst (render (PFalse :: Expr))
            actual <- checkAxiomUnsat axiom
            actual @?= True
        , testGroup
            "ordinary binders shadow global families in body and trigger"
            [ testCase name $ do
                actual <- checkTriggeredIdentity binders triggered
                actual @?= (False, True)
            | (name, binders, triggered) <-
                [ ("plain", [("family", intSort)], False)
                , ("default trigger", [("family", intSort)], True)
                , ("default trigger after unused family removal", [("unused", scheme), ("family", intSort)], True)
                ]
            ]
        ]
