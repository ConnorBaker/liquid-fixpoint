{-# LANGUAGE OverloadedStrings #-}

module SourceCheckScopeTests (qualifierTests, preparedCheckingTests) where

import Control.Monad.Reader (runReader)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Maybe (isNothing)
import qualified Language.Fixpoint.Horn.Info as Horn
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

qualifierTests :: TestTree
qualifierTests =
    testGroup
        "scraped qualifier scope"
        [ testCase "unbound symbols do not become global inference candidates" $
            Horn.scrapeFInfo Config.defConfig Config.Both (qualifierQuery missing mempty) @?= []
        , testCase "declared globals remain candidates" $ do
            let info = qualifierQuery missing (F.fromListSEnv [("external", F.FInt)])
                qs = Horn.scrapeFInfo Config.defConfig Config.Both info
            assertBool "closed predicate was lost" (not (null qs))
            assertBool "qualifier has free globals" (all (closed info) qs)
        , testCase "local binders become parameters" $ do
            let info = qualifierQuery (F.PAtom F.Ge (F.EVar "v") (F.ECon (F.I 0))) mempty
                qs = Horn.scrapeFInfo Config.defConfig Config.Both info
            assertBool "local predicate was lost" (not (null qs))
            assertBool "local variable escaped" (all (S.null . F.syms) qs)
        , testCase "disabled scraping remains empty" $
            Horn.scrapeFInfo Config.defConfig Config.No (qualifierQuery missing mempty) @?= []
        ]
  where
    missing = F.PAtom F.Eq (F.EVar "v") (F.EVar "external")
    closed info = all (`F.memberSEnv` C.globalEnv Config.defConfig info) . F.syms

qualifierQuery :: F.Expr -> F.SEnv F.Sort -> F.FInfo ()
qualifierQuery predicate globals =
    mempty
        { F.cm = M.fromList (F.addIds [F.mkSubC F.emptyIBindEnv lhs rhs Nothing [] ()])
        , F.gLits = globals
        }
  where
    lhs = F.RR F.FInt (F.Reft ("v", F.PTrue))
    rhs = F.RR F.FInt (F.Reft ("v", predicate))

preparedCheckingTests :: TestTree
preparedCheckingTests =
    testGroup
        "prepared checking scope"
        [ testCase "free function candidates have independent equations in both orders" $ do
            exprs [("f", F.FVar 9)] [integerCall, booleanCall] @?= [True, True]
            exprs [("f", F.FVar 9)] [booleanCall, integerCall] @?= [True, True]
        , testCase "one candidate still owns one coherent equation system" $
            exprs [("f", F.FVar 9)] [F.PAnd [integerCall, booleanCall]] @?= [False]
        , testCase "separate polymorphic occurrences remain independently instantiated" $
            exprs [("f", F.FAbs 0 (F.FFunc (F.FVar 0) (F.FVar 0)))] [F.PAnd [integerCall, booleanCall]] @?= [True]
        , testCase "deferred obligations and failed substitutions do not escape a call" $ do
            let bad = F.PAnd [F.PAtom F.Ueq (F.EVar "x") zero, equal (F.EVar "x") F.PTrue]
                good = equal (F.EVar "x") zero
            exprs [("x", F.FVar 9)] [bad, F.PTrue, good] @?= [False, True, True]
            exprs [("x", F.FVar 9)] [good, F.PTrue, bad] @?= [True, True, False]
        , testCase "raw fractional declaration survives a numeric value-binder shadow" $
            reft [("alpha", F.FFrac), ("x", F.FObj "alpha")] Nothing (F.RR F.FNum (F.Reft ("alpha", modulo))) @?= False
        , testCase "raw numeric declaration survives a fractional value-binder shadow" $
            reft [("alpha", F.FNum), ("x", F.FObj "alpha")] Nothing (F.RR F.FFrac (F.Reft ("alpha", modulo))) @?= True
        , testCase "the complete environment reserves unused free sort coordinates" $
            exprs
                [("f", resultScheme), ("unused", F.FVar 0)]
                [F.PAnd [freshBoolean, equal (F.EVar "unused") zero]]
                @?= [True]
        , testCase "each candidate reserves its own sort coordinates" $
            exprs
                [("f", resultScheme)]
                [F.PAnd [freshBoolean, equal (F.ECst zero (F.FVar 0)) zero]]
                @?= [True]
        , testCase "expected-sort coordinates are reserved before any occurrence opens" $ do
            let checkAt = C.checkSortAt (runReader (C.prepareSortCheck Nothing (F.fromListSEnv [("f", resultScheme)])) flags)
                body = F.ELam ("x", F.FVar 9) (F.PAnd [freshBoolean, equal (F.EVar "x") zero])
            assertBool "expected coordinate captured by fresh occurrence" $
                isNothing (checkAt F.dummySpan (Just (F.FFunc (F.FVar 0) F.boolSort)) body)
        , testCase "SortedReft retains the existing default expected-sort behavior" $
            reft [] (Just F.FInt) (F.RR F.boolSort (F.Reft ("value", F.PTrue))) @?= True
        ]
  where
    flags = Config.ElabFlags True False
    exprs :: [(F.Symbol, F.Sort)] -> [F.Expr] -> [Bool]
    exprs environment candidates =
        let checkAt = C.checkSortAt (runReader (C.prepareSortCheck Nothing (F.fromListSEnv environment)) flags)
         in map (isNothing . checkAt F.dummySpan Nothing) candidates
    reft :: [(F.Symbol, F.Sort)] -> Maybe F.Sort -> F.SortedReft -> Bool
    reft environment expected candidate =
        let checkAt = C.checkSortAt (runReader (C.prepareSortCheck Nothing (F.fromListSEnv environment)) flags)
         in isNothing (checkAt F.dummySpan expected candidate)
    zero :: F.Expr
    zero = F.ECon (F.I 0)
    equal :: F.Expr -> F.Expr -> F.Expr
    equal = F.PAtom F.Eq
    integerCall = equal (F.EApp (F.EVar "f") zero) zero
    booleanCall = equal (F.EApp (F.EVar "f") F.PTrue) F.PTrue
    resultScheme = F.FAbs 42 (F.FFunc F.FInt (F.FVar 42))
    freshBoolean = equal (F.EApp (F.EVar "f") zero) F.PTrue
    modulo = equal (F.EBin F.Mod (F.EVar "x") (F.ECon (F.I 2))) zero
