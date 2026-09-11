{-# LANGUAGE OverloadedStrings #-}

-- | Sort checking of the unification relations @~~@ and @!~@.
--
-- 'checkSortExpr' is pure and needs no solver, so these pin 'checkURel'
-- directly rather than through an @.fq@ round trip. That matters for more than
-- speed: a badly sorted @~~@ is rejected by the SOLVER, which fails the whole
-- query and exits 1 exactly as a well-formedness error does, so an end-to-end
-- test could not tell the two apart.
module SortCheckTests (tests) where

import           Control.Exception           (evaluate, try)
import           Data.List                   (isInfixOf)
import           Data.Maybe                  (isJust)
import           Language.Fixpoint.SortCheck (ElabParam (..), Elaborate (..), checkSortExpr)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config (ElabFlags (..))
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
  , binderTests
  ]

-- The public elaboration boundary must normalize bound-variable annotations
-- and body casts together. Checking only the final binder would miss the bug:
-- elab already normalizes that binder, but used to check its body first under
-- the unnormalized sort. Equality forces the cast to be checked in that body.
binderTests :: TestTree
binderTests = testGroup "binder theory-sort normalization"
  [ testGroup "accepted with matching body casts"
      [ testCase (binderName ++ "/" ++ sortName ++ "/arrays=" ++ show arrays) $ do
          let ef = ElabFlags arrays False
              body = PAtom Eq (ECst (EVar "x") s) (EVar "x")
              result = elaborate (ElabParam ef "binder regression" mempty) (bind s body)
              expected = resultSort (coerceSort ef s)
          _ <- evaluate (length (show result))
          checkSortExpr dummySpan emptySEnv result @?= Just expected
      | (binderName, bind, resultSort) <- binders
      , (sortName, s) <- sorts
      , arrays <- [False, True]
      ]
  , testGroup "rejected genuine cast mismatches"
      [ testCase (binderName ++ "/" ++ castName ++ "/arrays=" ++ show arrays) $ do
          let body = PAtom Eq (ECst (EVar "x") target) (EVar "x")
              result = elaborate (ElabParam (ElabFlags arrays False) "bad binder cast" mempty)
                         (bind source body)
          outcome <- try (evaluate (length (show result))) :: IO (Either Error Int)
          case outcome of
            Left err -> do
              let diagnostic = show err
              assertBool diagnostic ("Cannot cast" `isInfixOf` diagnostic)
              assertBool diagnostic ("incompatible sort" `isInfixOf` diagnostic)
            Right _ -> assertFailure "elaboration admitted an incompatible array cast"
      | (binderName, bind, _) <- binders
      , (castName, source, target) <- badCasts
      , arrays <- [False, True]
      ]
  ]
  where
    binders :: [(String, Sort -> Expr -> Expr, Sort -> Sort)]
    binders =
      [ ("lambda", \s -> ELam ("x", s), \s -> FFunc s boolSort)
      , ("forall", \s -> PAll [("x", s)], const boolSort)
      , ("exists", \s -> PExist [("x", s)], const boolSort)
      ]
    sorts :: [(String, Sort)]
    sorts =
      [ ("set", set)
      , ("bag", bag)
      , ("map", mapt)
      , ("array", array)
      , ("nested-set", setSort (setSort intSort))
      , ("nested-map", aggregate mapConName [set, bag])
      , ("nested-array", arraySort set bag)
      ]
    badCasts :: [(String, Sort, Sort)]
    badCasts =
      [ ("wrong-array-range", array, arraySort intSort intSort)
      , ("wrong-array-element", array, arraySort boolSort boolSort)
      , ("array-to-int", array, intSort)
      ]
