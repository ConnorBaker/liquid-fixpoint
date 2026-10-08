{-# LANGUAGE OverloadedStrings #-}

module EliminatedSharingSupport (Fixture, cfg, check, valid, sym, var, int, binding, kvar, use) where

import Control.Monad (forM_, unless)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.SortCheck as So
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types.Solutions as Sol
import NativeCallableTests (withSMT)

type Fixture = (F.SInfo (), Sol.Solution, F.SimpC ())

cfg :: C.Config
cfg = C.defConfig{C.allowHO = True, C.smtTimeout = Just 3000, C.save = False}

check :: String -> Bool -> Bool -> Fixture -> IO ()
check label expected reference fixture@(info, solution, constraint) = do
    let scope = S.insert "ghost" $ S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList (F.bs info)]
        initial = Solution.prepareSummaryState scope info
        (definitions, predicate) = Solution.lhsPredShared cfg initial scope F.emptyIBindEnv info solution constraint
    result <- valid fixture definitions predicate
    unless (result == expected) $ fail (label ++ ": unexpected shared result " ++ show result)
    if reference
        then do
            original <- valid fixture [] (Solution.lhsPred cfg scope F.emptyIBindEnv info solution constraint)
            unless (original == result) $ fail (label ++ ": differs from unfolded interpretation")
        else pure ()

valid :: Fixture -> [F.Equation] -> F.Expr -> IO Bool
valid (info, _, constraint) definitions predicate =
    withSMT (SMT.makeContextWithSEnv cfg "summary-controls" environment mempty) $ do
        forM_ definitions $ \equation ->
            SMT.smtDefineFunc (F.eqName equation) (F.eqArgs equation) (F.eqSort equation) (F.eqBody equation)
        SMT.smtAssert predicate
        SMT.smtAssert (F.PNot (F.crhs constraint))
        SMT.smtCheckUnsat
  where
    theory = So.theoryEnv cfg (mempty :: F.SInfo ())
    declarations = F.insertSEnv "ghost" F.FInt $ F.fromListSEnv [(name, F.sr_sort refinement) | (_, (name, refinement, _)) <- F.bindEnvToList (F.bs info)]
    environment = F.symEnv cfg (declarations <> (F.tsSort <$> theory)) theory [] mempty

sym :: String -> Int -> F.Symbol
sym prefix index = F.symbol (prefix ++ show index)

var :: F.Symbol -> F.Expr
var = F.EVar

int :: Integer -> F.Expr
int = F.ECon . F.I

binding :: F.BindId -> F.Symbol -> F.Sort -> F.Expr -> (F.BindId, (F.Symbol, F.SortedReft, ()))
binding index name sort predicate = (index, (name, F.RR sort (F.Reft (name, predicate)), ()))

kvar :: Int -> F.KVar
kvar = F.KV . sym "k"

use :: Int -> F.Symbol -> F.Expr
use index actual = F.PKVar (kvar index) mempty (F.toKVarSubst (M.singleton (sym "v" index) (var actual)))
