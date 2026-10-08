{-# LANGUAGE OverloadedStrings #-}

module ArrayConstantTests (tests) where

import Control.Monad (when)
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Theories as Theory
import qualified Language.Fixpoint.SortCheck as So
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import NativeCallableTests (withSMT)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "polymorphic constant arrays"
        [ testCase (show (solver, form, valid)) (check solver form valid)
        | solver <- [C.Z3, C.Cvc5]
        , form <- [Direct, Whole, Partial]
        , valid <- [True, False]
        ]

data Form = Direct | Whole | Partial deriving (Eq, Show)

check :: C.SMTSolver -> Form -> Bool -> Assertion
check solver form valid = do
    -- Both indices and values are quantified independently, including when
    -- one symbol is instantiated at different sorts in the same expression.
    fmap F.tsSort (F.lookupSEnv Theory.arrConstM theory)
        @?= Just (F.FAbs 0 (F.FAbs 1 (F.FFunc (F.FVar 1) (F.arraySort (F.FVar 0) (F.FVar 1)))))
    So.checkSortExpr Nothing F.dummySpan names expression @?= Just F.boolSort
    response <-
        withSMT (SMT.makeContextWithSEnv cfg "constant-arrays" environment mempty) $ do
            when (solver == C.Z3 && not valid) SMT.smtSetMbqi
            SMT.smtAssert elaborated
            SMT.command SMT.CheckSat
    response @?= if valid then SMT.Unsat else SMT.Sat
  where
    cfg = C.defConfig{C.solver = solver}
    theory = So.theoryEnv cfg (mempty :: F.SInfo ())
    names = F.tsSort <$> theory
    environment = F.symEnv cfg names theory [] mempty []
    expression =
        F.PNot $
            F.PAnd
                [ F.EEq (selected F.boolSort F.intSort F.PTrue (F.expr (7 :: Integer))) (F.expr (if valid then 7 else 8 :: Integer))
                , F.EEq (selected F.intSort F.boolSort (F.expr (3 :: Integer)) F.PTrue) F.PTrue
                ]
    selected indexSort valueSort index value = case form of
        Direct -> F.eApps (F.EVar Theory.arrSelectM) [array, index]
        Whole -> F.ELet "selectValue" (F.EVar Theory.arrSelectM) (F.eApps (F.EVar "selectValue") [array, index])
        Partial -> F.ELet "selectPartial" (F.EApp (F.EVar Theory.arrSelectM) array) (F.EApp (F.EVar "selectPartial") index)
      where
        array = F.ECst (F.EApp (F.EVar Theory.arrConstM) value) (F.arraySort indexSort valueSort)
    elaborated = So.elaborate (So.ElabParam (C.solverFlags cfg) "constant array" environment) expression
