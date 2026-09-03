{-# LANGUAGE OverloadedStrings #-}

-- | Sort checking of the unification relations @~~@ and @!~@.
--
-- 'checkSortExpr' is pure and needs no solver, so these pin 'checkURel'
-- directly rather than through an @.fq@ round trip. That matters for more than
-- speed: a badly sorted @~~@ is rejected by the SOLVER, which fails the whole
-- query and exits 1 exactly as a well-formedness error does, so an end-to-end
-- test could not tell the two apart.
module SortCheckTests (tests) where

import           Data.Maybe                  (isJust)
import           Language.Fixpoint.SortCheck (checkSortExpr)
import           Language.Fixpoint.Types
import           Test.Tasty
import           Test.Tasty.HUnit

aggregate :: Symbol -> [Sort] -> Sort
aggregate c = fAppTC (symbolFTycon (dummyLoc c))

set, bag, array, mapt :: Sort
set   = aggregate setConName   [intSort]
bag   = aggregate bagConName   [intSort]
array = aggregate arrayConName [intSort, boolSort]
mapt  = aggregate mapConName   [intSort, intSort]

-- | Is @x r y@ well sorted, with @x@ at @s1@ and @y@ at @s2@?
accepts :: Sort -> Brel -> Sort -> Bool
accepts s1 r s2 =
  isJust (checkSortExpr dummySpan env (PAtom r (EVar "x") (EVar "y")))
  where
    env = fromListSEnv [("x", s1), ("y", s2)]

-- | Both relations route to 'checkURel', from separate equations of
-- 'checkRelTy', so every case is stated for each.
both :: String -> Sort -> Sort -> Bool -> [TestTree]
both n s1 s2 expected =
  [ testCase (n ++ " (" ++ show r ++ ")") (accepts s1 r s2 @?= expected)
  | r <- [Ueq, Une]
  ]

tests :: TestTree
tests = testGroup "checkURel"
  [ testGroup "REJECTED: an aggregate against an Int-represented sort" $ concat
      [ both "Set  ~~ int" set   intSort False
      , both "Bag  ~~ int" bag   intSort False
      , both "Array ~~ int" array intSort False
        -- The operands are compared symmetrically, so the mirror must fail too.
      , both "int  ~~ Set" intSort set   False
      ]

  , testGroup "REJECTED: two different aggregates" $ concat
      [ both "Set ~~ Bag"   set bag   False
      , both "Set ~~ Array" set array False
      , both "Bag ~~ Array" bag array False
      ]

  , testGroup "ACCEPTED: one aggregate against itself" $ concat
      [ both "Set  ~~ Set"   set   set   True
      , both "Bag  ~~ Bag"   bag   bag   True
      , both "Array ~~ Array" array array True
      ]

  , testGroup "ACCEPTED: the Int-represented sorts, including Map_t" $ concat
      [ both "int  ~~ int"  intSort  intSort  True
      , both "bool ~~ bool" boolSort boolSort True
        -- 'fappSmtSort' has no branch for 'Map_t', so a map is Int-represented
        -- and must stay admissible against an Int. This is the case that would
        -- regress if 'mapConName' were added to 'smtAggregateHead'.
      , both "Map  ~~ Map"  mapt     mapt     True
      , both "Map  ~~ int"  mapt     intSort  True
      ]

  , testGroup "ACCEPTED: unchanged, only the head is compared" $ concat
      [ -- Set Int and Set Bool are distinct SMT sorts; this is deliberately
        -- still admitted, so the check cannot be read as making ~~ sound.
        both "Set int ~~ Set bool"
             (aggregate setConName [intSort])
             (aggregate setConName [boolSort])
             True
        -- A partially applied Array_t is not an aggregate to 'fappSmtSort'
        -- either, so it must not be one here.
      , both "Array/1 ~~ int" (aggregate arrayConName [intSort]) intSort True
      ]

  , testGroup "REJECTED already: bool against non-bool, unchanged by this patch"
      [ testCase "int ~~ bool" (accepts intSort Ueq boolSort @?= False) ]
  ]
