{-# LANGUAGE OverloadedStrings #-}

-- | Witness projection must not re-traverse the clauses a witness cannot
-- change. Projection eliminates one witness at a time; each step used to
-- substitute into, re-split and re-judge every remaining clause, so its work
-- was the number of witnesses times the size of the conjunction. A clause
-- without binders or KVar applications that does not mention the eliminated
-- name is unchanged by that substitution and keeps its judgments.
--
-- The discriminator observes the work, not the result (which is the same
-- either way): with the large clauses fixed, doubling the number of
-- witnesses must not double the allocation of the projection. Re-traversing
-- them at every step makes the allocation proportional to the witness count
-- (a ratio near 2); traversing them once leaves it nearly constant.
module ProjectionCostTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import qualified Language.Fixpoint.Solver.Solution as F
import qualified Language.Fixpoint.Types as F
import System.Mem (getAllocationCounter, performMajorGC)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "witness projection cost"
    [ testCase "projection eliminates every witness and keeps the large clauses" $
        F.simplifyKVar declarations mempty (input witnessesSmall) @?= expected
    , testCase "large clauses that no witness mentions are traversed once, not per witness" $ do
        small <- allocation (input witnessesSmall)
        large <- allocation (input witnessesLarge)
        let ratio = fromIntegral large / fromIntegral small :: Double
        assertBool
          ( "allocation grew "
              ++ show ratio
              ++ "x when the witness count doubled ("
              ++ show small
              ++ " -> "
              ++ show large
              ++ " bytes); bound is "
              ++ show bound
          )
          (ratio < bound)
    ]
  where
    -- Re-traversal gives a ratio near 2; a single traversal near 1. The
    -- midpoint leaves margin for optimisation-level differences either way.
    bound = 1.5

witnessesSmall, witnessesLarge, clauseCount, clauseSize :: Int
witnessesSmall = 40
witnessesLarge = 2 * witnessesSmall
clauseCount = 10
clauseSize = 4000

declarations :: F.SEnv F.Sort
declarations = F.fromListSEnv [("A", F.FInt)]

-- | Large closed clauses, distinct at their roots so deduplication rejects
-- them immediately, and none an equality, so none is a witness.
largeClauses :: [F.Expr]
largeClauses =
  [ F.PAtom F.Gt (F.EBin F.Plus (F.ECon (F.I (fromIntegral i))) sumOfA) (F.ECon (F.I 0))
  | i <- [1 .. clauseCount]
  ]
  where
    sumOfA = foldr1 (F.EBin F.Plus) (replicate clauseSize (F.EVar "A"))

witnessNames :: Int -> [F.Symbol]
witnessNames w = [F.symbol ("x" ++ show i) | i <- [1 .. w]]

input :: Int -> F.Expr
input w =
  F.PExist
    [(x, F.FInt) | x <- witnessNames w]
    (F.PAnd ([F.PAtom F.Eq (F.EVar x) (F.ECon (F.I (fromIntegral i))) | (i, x) <- zip [1 :: Int ..] (witnessNames w)] ++ largeClauses))

-- | Every witness is eliminated and no large clause mentions one.
expected :: F.Expr
expected = F.PAnd largeClauses

allocation :: F.Expr -> IO Integer
allocation e = do
  inputE <- evaluate (force e)
  performMajorGC
  before <- getAllocationCounter
  result <- evaluate (force (F.simplifyKVar declarations mempty inputE))
  after <- getAllocationCounter
  result @?= expected
  -- The counter counts down.
  pure (fromIntegral (before - after))
