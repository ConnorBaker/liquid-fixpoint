{-# LANGUAGE OverloadedStrings #-}

-- | An exported eliminated solution closes its own defining environment once.
--
-- Global witnesses g0..g(G-1) are in the environment of every constraint, so
-- they are common binders ('Sol.sScp') of every KVar. A chain of eliminated
-- definitions k0 <- k1 <- ... <- kn has each ki defined from a binder refined
-- by k(i-1). Exporting kn closes kn's complete environment, which holds every
-- global fact. A nested definition occurs in a binder of that environment, so
-- re-closing the global facts there repeats them once per nesting level: the
-- export of a chain twice as long held twice as many copies of each global
-- fact, and the global environment's size multiplied every summary.
module ExportScopeTests (tests) where

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Language.Fixpoint.Graph as Graph
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Eliminate as Eliminate
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types.Solutions as Sol
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "eliminated export scope"
    [ testCase "a chain's export closes each global fact once, whatever its length" $ do
        short <- globalFacts 4
        long <- globalFacts 8
        assertBool ("the export closes the global facts: " ++ show short) (short >= 1)
        assertEqual "copies of g0's fact in the exports of chains of 4 and 8 definitions" short long
    , testCase "every link of the chain is eliminated and exported" $ do
        delayed <- exports Witnesses 8
        assertBool "every chain KVar is exported" (all ((`M.member` delayed) . kvar) [0 .. 8])
    , -- LiquidHaskell's WF environments hold every binder in scope, so its
      -- globals are also each KVar's formals.
      testCase "with the globals as formals, a chain's export closes each global fact a fixed number of times" $ do
        short <- globalFactsAs Formals 4
        long <- globalFactsAs Formals 8
        assertEqual "copies of g0's fact in the exports of chains of 4 and 8 definitions" short long
    , testCase "with the globals as formals, every link of the chain is eliminated and exported" $ do
        delayed <- exports Formals 8
        assertBool "every chain KVar is exported" (all ((`M.member` delayed) . kvar) [0 .. 8])
    ]

-- | Whether the globals are in each KVar's WF environment (its formals).
data Globals = Witnesses | Formals

globals :: Int
globals = 40

config :: C.Config
config = C.defConfig{C.eliminate = C.Some, C.cores = Just 1, C.noEnvReduction = True, C.save = False}

kvar :: Int -> F.KVar
kvar i = F.KV (F.symbol ("k" ++ show i))

g :: Int -> F.Symbol
g i = F.symbol ("g" ++ show i)

y :: Int -> F.Symbol
y j = F.symbol ("y" ++ show j)

-- | Global facts are inequalities, which projection cannot substitute away.
-- As witnesses, no KVar's WF environment holds the globals; as formals,
-- every KVar's does.
query :: Globals -> Int -> F.FInfo ()
query globalsAre n =
  mempty
    { F.bs = F.bindEnvFromList (gs ++ ys)
    , F.cm = M.fromList [(F.subcId c, c) | c <- map definition [0 .. n]]
    , F.ws = M.fromList [(kvar i, F.WfC formals [("vv", F.FInt)] (kvar i) ()) | i <- [0 .. n]]
    }
  where
    formals = case globalsAre of
      Witnesses -> mempty
      Formals -> common
    gs = [(i, (g i, F.RR F.FInt (F.Reft (g i, F.PAtom F.Gt (F.EVar (g i)) (F.ECon (F.I (fromIntegral i))))), ())) | i <- [0 .. globals - 1]]
    ys = [(globals + j, (y j, F.RR F.FInt (F.Reft (y j, occurrence (j - 1) (F.EVar (y j)))), ())) | j <- [1 .. n]]
    common = F.fromListIBindEnv [0 .. globals - 1]
    occurrence k actual = F.PKVar (kvar k) mempty (F.toKVarSubst (M.singleton "vv" actual))
    definition 0 = constraint 0 common (F.PAtom F.Gt (F.EVar "vv") (F.EVar (g 0))) (occurrence 0 (F.EVar "vv"))
    definition j =
      constraint
        (fromIntegral j)
        (F.insertsIBindEnv [globals + j] common)
        (F.PAtom F.Gt (F.EVar "vv") (F.EVar (y j)))
        (occurrence j (F.EVar "vv"))
    constraint index context lhs rhs =
      F.mkSubC context (F.RR F.FInt (F.Reft ("vv", lhs))) (F.RR F.FInt (F.Reft ("vv", rhs))) (Just index) [] ()

exports :: Globals -> Int -> IO F.FixDelayedSolution
exports globalsAre n = do
  (_, _, prepared, _) <- Solver.simplifyFInfo config (query globalsAre n)
  let solution = Graph.siSol (Eliminate.solverInfo config prepared)
      scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList (F.bs prepared)]
  pure (Solution.nonCutsResult config scope prepared solution)

-- | Copies of g0's fact (g0 > 0) in the export of the chain's last KVar.
globalFacts :: Int -> IO Int
globalFacts = globalFactsAs Witnesses

globalFactsAs :: Globals -> Int -> IO Int
globalFactsAs globalsAre n = do
  delayed <- exports globalsAre n
  export <- maybe (assertFailure "the chain's last KVar is exported") pure (M.lookup (kvar n) delayed)
  pure (count (F.forceDelayed export))
  where
    count e = (if isFact e then 1 else 0) + sum (map count (children e))
    -- Only g0's fact compares with the constant 0.
    isFact (F.PAtom F.Gt _ right) = constant right == Just 0
    isFact _ = False
    constant (F.ECst e _) = constant e
    constant (F.ECon (F.I i)) = Just i
    constant _ = Nothing
    children e = case e of
      F.EApp a b -> [a, b]
      F.ENeg a -> [a]
      F.EBin _ a b -> [a, b]
      F.EIte a b c -> [a, b, c]
      F.ECst a _ -> [a]
      F.ELam _ a -> [a]
      F.ELet _ a b -> [a, b]
      F.ETApp a _ -> [a]
      F.ETAbs a _ -> [a]
      F.PAnd xs -> xs
      F.POr xs -> xs
      F.PNot a -> [a]
      F.PImp a b -> [a, b]
      F.PIff a b -> [a, b]
      F.PAtom _ a b -> [a, b]
      F.PAll _ a -> [a]
      F.PExist _ a -> [a]
      F.ECoerc _ _ a -> [a]
      _ -> []
