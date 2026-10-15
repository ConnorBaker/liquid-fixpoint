{-# LANGUAGE OverloadedStrings #-}

-- | One query's eliminated exports share the projections of the definitions
-- they reach. Every export interprets nested eliminated definitions in their
-- own defining environments, so exports that reach the same definition used
-- to project it once each.
--
-- The query has one expensive definition k0 (an environment of many witness
-- equalities) and m cheap definitions k1..km that each mention it. Forcing all
-- exports must project k0 once, not m times: doubling m must not double the
-- allocation. Sharing must not change any export: forcing one export alone
-- and after all the others gives the same value.
module ExportSharingTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Language.Fixpoint.Graph as Graph
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Eliminate as Eliminate
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Types.Solutions as Sol
import System.Mem (getAllocationCounter, performMajorGC)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "eliminated export sharing"
    [ testCase "an export is the same alone and after the exports it shares with" $ do
        alone <- exports users
        shared <- exports users
        _ <- evaluate (force [F.forceDelayed (shared M.! kvar i) | i <- [users, users - 1 .. 0]])
        let one = F.forceDelayed (alone M.! kvar 1)
            again = F.forceDelayed (shared M.! kvar 1)
        assertBool "the expensive definition is eliminated" (M.member (kvar 0) alone)
        assertBool "every user is eliminated" (all ((`M.member` alone) . kvar) [1 .. users])
        again @?= one
        show again @?= show one
    , testCase "exports reaching one definition project it once" $ do
        small <- allocation users
        large <- allocation (2 * users)
        let ratio = fromIntegral large / fromIntegral small :: Double
        assertBool
          ( "allocation grew "
              ++ show ratio
              ++ "x when the users of one definition doubled ("
              ++ show small
              ++ " -> "
              ++ show large
              ++ " bytes); bound is "
              ++ show bound
          )
          (ratio < bound)
    ]
  where
    -- Projecting the shared definition per export gives a ratio near 2.
    bound = 1.5

users, witnesses :: Int
users = 8
witnesses = 600

config :: C.Config
config = C.defConfig{C.eliminate = C.Some, C.cores = Just 1, C.noEnvReduction = True, C.save = False}

kvar :: Int -> F.KVar
kvar i = F.KV (F.symbol ("k" ++ show i))

-- | k0's defining environment holds many witness equalities; each ki is
-- defined from a binder refined by k0.
query :: Int -> F.FInfo ()
query m =
  mempty
    { F.bs = F.bindEnvFromList (xs ++ ys)
    , F.cm = M.fromList [(F.subcId c, c) | c <- definition : uses]
    , F.ws = M.fromList [(kvar i, F.WfC mempty [("vv", F.FInt)] (kvar i) ()) | i <- [0 .. m]]
    }
  where
    xs = [(i, (x i, F.RR F.FInt (F.Reft (x i, F.EEq (F.EVar (x i)) (F.ECon (F.I (fromIntegral i))))), ())) | i <- [0 .. witnesses - 1]]
    ys = [(witnesses + j, (y j, F.RR F.FInt (F.Reft (y j, occurrence 0 (F.EVar (y j)))), ())) | j <- [1 .. m]]
    x i = F.symbol ("x" ++ show i)
    y j = F.symbol ("y" ++ show j)
    occurrence k actual = F.PKVar (kvar k) mempty (F.toKVarSubst (M.singleton "vv" actual))
    definition =
      constraint 0 (F.fromListIBindEnv [0 .. witnesses - 1]) (F.EEq (F.EVar "vv") (foldr1 (F.EBin F.Plus) (map (F.EVar . x) [0 .. witnesses - 1]))) (occurrence 0 (F.EVar "vv"))
    uses =
      [ constraint (fromIntegral j) (F.fromListIBindEnv [witnesses + j]) (F.EEq (F.EVar "vv") (F.EVar (y j))) (occurrence j (F.EVar "vv"))
      | j <- [1 .. m]
      ]
    constraint index context lhs rhs =
      F.mkSubC context (F.RR F.FInt (F.Reft ("vv", lhs))) (F.RR F.FInt (F.Reft ("vv", rhs))) (Just index) [] ()

exports :: Int -> IO F.FixDelayedSolution
exports m = do
  (_, _, prepared, _) <- Solver.simplifyFInfo config (query m)
  let solution = Graph.siSol (Eliminate.solverInfo config prepared)
      scope = S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList (F.bs prepared)]
  assertBool "eliminated definitions" (not (M.null (Sol.sHyp solution)))
  pure (Solution.nonCutsResult config scope prepared solution)

allocation :: Int -> IO Integer
allocation m = do
  delayed <- exports m
  performMajorGC
  before <- getAllocationCounter
  _ <- evaluate (force [F.forceDelayed (delayed M.! kvar i) | i <- [1 .. m]])
  after <- getAllocationCounter
  pure (fromIntegral (before - after))
