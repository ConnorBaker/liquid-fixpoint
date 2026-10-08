{-# LANGUAGE MultilineStrings #-}
{-# LANGUAGE OverloadedStrings #-}

module SimplifyKVarTests (tests) where

import Control.Monad (when)
import qualified Data.Generics as Generics
import qualified Data.HashSet as S
import Language.Fixpoint.Parse
import qualified Language.Fixpoint.Solver.Solution as F
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup "simplifyKVar" $
    map
      simplificationTest
      [ SimplificationTest
          { name = "single elimination"
          , declarations = binaryDeclarations
          , expected =
              """
              exists [y : int] . P C y
              """
          , input =
              """
              exists [x : int, y : int] . x == C && P x y
              """
          }
      , SimplificationTest
          { name = "full elimination"
          , declarations = binaryDeclarations
          , expected =
              """
              P C D
              """
          , input =
              """
              exists [x : int, y : int] . x == C && P x y && y == D
              """
          }
      , SimplificationTest
          { name = "alpha equivalence"
          , declarations = binaryDeclarations
          , expected =
              """
              (exists [w : int, z : int] . Q w z) &&
              (exists [w : int, z : int] . P w z)
              """
          , input =
              """
              (exists [w : int, z : int] . Q w z) &&
              (exists [w : int, z : int] . P w z) &&
              (exists [x : int, y : int] . P x y)
              """
          }
      , SimplificationTest
          { name = "floating"
          , declarations = binaryDeclarations
          , expected =
              """
              (exists [x : int, y : int] . P x y) && A == C
              """
          , input =
              """
              exists [x : int, y : int] . A == C && P x y
              """
          }
      , SimplificationTest
          { name = "inner floating"
          , declarations = [("P", F.FFunc F.FInt F.boolSort), ("Q", F.FFunc F.FInt F.boolSort)]
          , expected =
              """
              (exists [x : int] . P x && Q x) && (exists [y : int] . P y)
              """
          , input =
              """
              exists [x : int] . P x && (exists [ y : int] . P y && Q x)
              """
          }
      , largeSimplificationTest
      ]
      ++ projectionTests
      ++ alphaTests

binaryDeclarations :: [(F.Symbol, F.Sort)]
binaryDeclarations =
  [("P", predicate), ("Q", predicate), ("A", F.FInt), ("C", F.FInt), ("D", F.FInt)]
 where
  predicate = F.mkFFunc 0 [F.FInt, F.FInt, F.boolSort]

data SimplificationTest = SimplificationTest
  { input :: String
  , expected :: String
  , name :: String
  , declarations :: [(F.Symbol, F.Sort)]
  }

simplificationTest :: SimplificationTest -> TestTree
simplificationTest test =
  testCase (name test) $ do
    let actual0 = doParse'' True predP (name test) (input test)
        environment = F.fromListSEnv (declarations test)
        actual = F.simplifyKVar environment mempty actual0
        expectedE = doParse'' True predP (name test) (expected test)
        allScope = F.syms [actual, expectedE]
    mapM_ (assertPredicate environment mempty) [actual0, actual, expectedE]
    F.syms actual @?= F.syms expectedE
    when (not $ F.alphaEq allScope actual expectedE) $ do
      assertFailure $
        unlines
          [ "output is not as expected"
          , "Expected:"
          , expected test
          , ""
          , "Actual:"
          , F.showpp actual
          ]

assertPredicate :: F.SEnv F.Sort -> F.SEnv F.Sort -> F.Expr -> Assertion
assertPredicate environment locals expression =
  case C.sortExprE Nothing F.dummySpan environment locals expression of
    Left failure -> assertFailure (show failure)
    Right sort -> sort @?= F.boolSort

projectionTests :: [TestTree]
projectionTests =
  [ unchanged "mixed numeric equality is not an exact witness" mempty mempty $
      existsInt (equal x (F.ECon (F.R 0.5)))
  , unchanged "a widening cast is not a bound variable witness" mempty mempty $
      existsInt (equal (F.ECst x F.FReal) (F.ECon (F.R 0.5)))
  , unchanged "uninterpreted equality is not a witness" mempty mempty $
      existsInt (F.PAtom F.Ueq x zero)
  , unchanged "a witness cannot contain the eliminated variable" mempty mempty $
      existsInt (equal x (F.EBin F.Plus x zero))
  , unchanged "canonical locals shadow declaration terms" (F.fromListSEnv [("y", F.FInt)]) (F.fromListSEnv [("y", F.FReal)]) $
      existsInt (equal x y)
  , projection
      "retains a witness's occurrence type application"
      (F.fromListSEnv [("f", F.FAbs 0 (F.FVar 0))])
      mempty
      (existsInt (F.PAnd [equal x (F.ECst (F.EVar "f") F.FInt), F.PAtom F.Gt x zero]))
      (F.PAtom F.Gt (F.ECst (F.EVar "f") F.FInt) zero)
  , unchanged
      "fresh inference coordinates do not justify erasing type applications"
      (F.fromListSEnv (("f", F.FAbs 0 (F.FVar 0)) : [(F.symbol ("occupied" ++ show i), F.FVar i) | i <- [1 .. 4]]))
      mempty
      $ equal (F.ECst (F.EVar "f") (F.FVar 5)) (F.EVar "f")
  , unchanged
      "an unused scheme binder still requires its occurrence type application"
      (F.fromListSEnv [("f", F.FAbs 0 F.FInt)])
      mempty
      $ equal (F.ECst (F.EVar "f") F.FInt) (F.EVar "f")
  , unchanged "nominally equal constructors with different string carriers are distinct" (F.fromListSEnv [("y", stringConstructor)]) mempty $
      F.PExist [("x", ordinaryConstructor)] (equal x y)
  , testCase "retains numeric capability without forcing unrelated metadata" $ do
      let numeric = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc "NumericWitness") True (error "fractional capability must stay lazy"))
          opaque = F.FTC (F.symbolNumInfoFTyCon (F.dummyLoc "NumericWitness") False (error "fractional capability must stay lazy"))
          environment = F.fromListSEnv [("y", opaque)]
          inputE = F.PExist [("x", numeric)] (F.PAnd [equal x y, equal (F.ENeg x) x])
          expectedE = equal (F.ENeg (F.ECst y numeric)) (F.ECst y numeric)
      let actual = F.simplifyKVar environment mempty inputE
      mapM_ (assertPredicate environment mempty) [inputE, actual]
      actual @?= expectedE
  , testCase "witness substitution preserves a free name under a nested binder" $ do
      let environment = F.fromListSEnv (("z", F.FInt) : binaryDeclarations)
          inputE = parse "exists [x : int] . x == z && (exists [z : int] . P x z)"
          expectedE = parse "exists [w : int] . P z w"
          actual = F.simplifyKVar environment mempty inputE
      mapM_ (assertPredicate environment mempty) [inputE, actual]
      F.syms actual @?= F.syms expectedE
      assertBool "capture-avoiding result" (F.alphaEq S.empty actual expectedE)
  ]
 where
  x = F.EVar "x"
  y = F.EVar "y"
  zero = F.ECon (F.I 0)
  equal = F.PAtom F.Eq
  existsInt = F.PExist [("x", F.FInt)]
  unchanged label environment locals expression = projection label environment locals expression expression

projection :: String -> F.SEnv F.Sort -> F.SEnv F.Sort -> F.Expr -> F.Expr -> TestTree
projection label environment locals inputE expectedE =
  testCase label $ do
    let actual = F.simplifyKVar environment locals inputE
    mapM_ (assertPredicate environment locals) [inputE, actual, expectedE]
    actual @?= expectedE

alphaTests :: [TestTree]
alphaTests =
  [ alpha "renamed binders" True "exists [x : int] . P x z" "exists [y : int] . P y z"
  , alpha "a free name is not a bound name" False "exists [x : int] . P z x" "exists [z : int] . P z z"
  , alpha "binder arity matters" False "exists [x : int] . P x z" "exists [x : int, y : int] . P x z"
  , alpha "binder sorts matter" False "exists [x : int] . P x z" "exists [x : real] . P x z"
  , alpha "nested shadowing" True "exists [x : int] . P x z && (exists [x : int] . Q x z)" "exists [y : int] . P y z && (exists [w : int] . Q w z)"
  , testCase "type applications are not erased for comparison" $
      F.alphaEq S.empty (F.ECst (F.EVar "f") F.FInt) (F.ECst (F.EVar "f") F.FReal) @?= False
  , testCase "constructor carrier metadata matters in annotations" $
      F.alphaEq S.empty (F.ECst (F.EVar "f") ordinaryConstructor) (F.ECst (F.EVar "f") stringConstructor) @?= False
  , testCase "constructor carrier metadata matters in binder sorts" $
      F.alphaEq S.empty (F.PExist [("x", ordinaryConstructor)] F.PTrue) (F.PExist [("x", stringConstructor)] F.PTrue) @?= False
  ]
 where
  alpha label expectedResult left right =
    testCase label $
      F.alphaEq S.empty (parse left) (parse right) @?= expectedResult

parse :: String -> F.Expr
parse = doParse'' True predP "typed simplification regression"

ordinaryConstructor, stringConstructor :: F.Sort
ordinaryConstructor = F.FTC (F.symbolFTycon (F.dummyLoc "CarrierWitness"))
-- The public serialization instances can carry metadata not produced by the
-- standard named constructors. Exercise that representation through Data.
stringConstructor =
  Generics.everywhereBut
    (Generics.mkQ False (const True :: F.Symbol -> Bool))
    (Generics.mkT (const True :: Bool -> Bool))
    ordinaryConstructor

largeSimplificationTest :: SimplificationTest
largeSimplificationTest =
  SimplificationTest
    { name = "large simplification"
    , declarations =
        [ ("i##aS7", F.FInt)
        , ("Test.gt0xy", F.mkFFunc 0 [F.FInt, F.FInt, F.boolSort])
        , ("lq_anf##7205759403792798198##d1ca", fixtureSort "(GHC.Internal.Base.Monad (Test.State int))")
        , ("lq_anf##7205759403792798199##d1cb", fixtureSort "(Test.State int Tuple0)")
        , ("lq_anf##7205759403792798200##d1cc", fixtureSort "(Test.State int int)")
        ]
    , expected =
        """
        exists [w : int] . Test.gt0xy w i##aS7
        """
    , input =
        """
        exists [VV##1821##k_ : int,
                i##aS7##k_ : int,
                lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                lq_tmpx##1823##k_ : int,
                lq_tmpx##1824##k_ : int]
              . (exists [w : int,
                         w2 : int,
                         x : int,
                         y : Tuple0,
                         VV##F##13 : int]
                   . VV##1821##k_ == VV##F##13
                     && i##aS7##k_ == i##aS7
                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                     && lq_tmpx##1823##k_ == w
                     && lq_tmpx##1824##k_ == x
                     && (exists [VV##1829 : int,
                                 lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                 lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                 VV##1805##k_ : int,
                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                 i##aS7##k_ : int]
                           . VV##1829 == w
                             && VV##1805##k_ == w
                             && i##aS7##k_ == i##aS7
                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                             && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                             && (exists [VV##F##3 : int]
                                   . Test.gt0xy VV##F##3 i##aS7
                                     && VV##1805##k_ == VV##F##3
                                     && i##aS7##k_ == i##aS7
                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                     && (exists [VV##1830 : int,
                                 lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                 i##aS7##k_ : int,
                                 lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                 VV##1807##k_ : int]
                           . VV##1830 == w2
                             && VV##1807##k_ == w2
                             && i##aS7##k_ == i##aS7
                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                             && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                             && (exists [w : int,
                                         VV##F##14 : int,
                                         lq_rnmx##255 : Tuple0]
                                   . (exists [VV##1828 : int,
                                              lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                              lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                              VV##1805##k_ : int,
                                              lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                              i##aS7##k_ : int]
                                        . VV##1828 == w
                                          && VV##1805##k_ == w
                                          && i##aS7##k_ == i##aS7
                                          && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                          && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                          && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                          && (exists [VV##F##3 : int]
                                                . Test.gt0xy VV##F##3 i##aS7
                                                  && VV##1805##k_ == VV##F##3
                                                  && i##aS7##k_ == i##aS7
                                                  && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                  && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                  && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                                     && (exists [lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                                 i##aS7##k_ : int,
                                                 lq_tmpx##1812##k_ : Tuple0,
                                                 VV##1809##k_ : int,
                                                 lq_tmpx##1811##k_ : int,
                                                 lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int)]
                                           . VV##1809##k_ == VV##F##14
                                             && i##aS7##k_ == i##aS7
                                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                             && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                             && lq_tmpx##1811##k_ == w
                                             && lq_tmpx##1812##k_ == lq_rnmx##255
                                             && (exists [VV##F##12 : int,
                                                         lq_tmpx##1811 : int,
                                                         lq_tmpx##1812 : Tuple0,
                                                         lq_tmpdb##43 : int,
                                                         lq_tmpdb##44 : Tuple0]
                                                   . VV##F##12 == i##aS7
                                                     && VV##1809##k_ == VV##F##12
                                                     && i##aS7##k_ == i##aS7
                                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                                     && lq_tmpx##1811##k_ == lq_tmpx##1811
                                                     && lq_tmpx##1812##k_ == lq_tmpx##1812))
                                     && (exists [i##aS7##k_ : int,
                                                 lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                                 lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                                 lq_tmpx##1801 : Tuple0,
                                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                                 VV##1799##k_ : Tuple0]
                                           . VV##1799##k_ == lq_rnmx##255
                                             && i##aS7##k_ == i##aS7
                                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                             && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                             && lq_tmpx##1801 == lq_rnmx##255
                                             && (exists [VV##F##10 : Tuple0]
                                                   . VV##1799##k_ == VV##F##10
                                                     && i##aS7##k_ == i##aS7
                                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                                     && VV##1807##k_ == VV##F##14
                                     && i##aS7##k_ == i##aS7
                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                     && (exists [i##aS7##k_ : int,
                                 lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                 lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                 lq_tmpx##1801 : Tuple0,
                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                 VV##1799##k_ : Tuple0]
                           . VV##1799##k_ == y
                             && i##aS7##k_ == i##aS7
                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                             && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                             && lq_tmpx##1801 == y
                             && (exists [VV##F##10 : Tuple0]
                                   . VV##1799##k_ == VV##F##10
                                     && i##aS7##k_ == i##aS7
                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                     && (exists [i##aS7##k_ : int,
                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                 lq_tmpx##1804 : int,
                                 lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                 lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                 VV##1802##k_ : int]
                           . VV##1802##k_ == x
                             && i##aS7##k_ == i##aS7
                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                             && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                             && lq_tmpx##1804 == x
                             && (exists [VV##F##6 : int]
                                   . (exists [i##aS7##k_ : int,
                                              lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                              lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                              VV##1796##k_ : int]
                                        . VV##1796##k_ == VV##F##6
                                          && i##aS7##k_ == i##aS7
                                          && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                          && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                          && (exists [VV##F##7 : int]
                                                . (exists [lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                                           lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                                           i##aS7##k_ : int,
                                                           lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                                           VV##1807##k_ : int]
                                                     . VV##1807##k_ == VV##F##7
                                                       && i##aS7##k_ == i##aS7
                                                       && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                       && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                       && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                                       && (exists [w : int,
                                                                   VV##F##14 : int,
                                                                   lq_rnmx##255 : Tuple0]
                                                             . (exists [VV##1828 : int,
                                                                        lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                                                        lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                                                        VV##1805##k_ : int,
                                                                        lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                                                        i##aS7##k_ : int]
                                                                  . VV##1828 == w
                                                                    && VV##1805##k_ == w
                                                                    && i##aS7##k_ == i##aS7
                                                                    && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                                    && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                                    && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                                                    && (exists [VV##F##3 : int]
                                                                          . Test.gt0xy VV##F##3 i##aS7
                                                                            && VV##1805##k_ == VV##F##3
                                                                            && i##aS7##k_ == i##aS7
                                                                            && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                                            && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                                            && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                                                               && (exists [lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                                                           lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                                                           i##aS7##k_ : int,
                                                                           lq_tmpx##1812##k_ : Tuple0,
                                                                           VV##1809##k_ : int,
                                                                           lq_tmpx##1811##k_ : int,
                                                                           lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int)]
                                                                     . VV##1809##k_ == VV##F##14
                                                                       && i##aS7##k_ == i##aS7
                                                                       && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                                       && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                                       && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                                                       && lq_tmpx##1811##k_ == w
                                                                       && lq_tmpx##1812##k_ == lq_rnmx##255
                                                                       && (exists [VV##F##12 : int,
                                                                                   lq_tmpx##1811 : int,
                                                                                   lq_tmpx##1812 : Tuple0,
                                                                                   lq_tmpdb##43 : int,
                                                                                   lq_tmpdb##44 : Tuple0]
                                                                             . VV##F##12 == i##aS7
                                                                               && VV##1809##k_ == VV##F##12
                                                                               && i##aS7##k_ == i##aS7
                                                                               && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                                               && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                                               && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                                                               && lq_tmpx##1811##k_ == lq_tmpx##1811
                                                                               && lq_tmpx##1812##k_ == lq_tmpx##1812))
                                                               && (exists [i##aS7##k_ : int,
                                                                           lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                                                           lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                                                           lq_tmpx##1801 : Tuple0,
                                                                           lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                                                           VV##1799##k_ : Tuple0]
                                                                     . VV##1799##k_ == lq_rnmx##255
                                                                       && i##aS7##k_ == i##aS7
                                                                       && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                                       && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                                       && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                                                       && lq_tmpx##1801 == lq_rnmx##255
                                                                       && (exists [VV##F##10 : Tuple0]
                                                                             . VV##1799##k_ == VV##F##10
                                                                               && i##aS7##k_ == i##aS7
                                                                               && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                                               && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                                               && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                                                               && VV##1807##k_ == VV##F##14
                                                               && i##aS7##k_ == i##aS7
                                                               && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                               && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                                               && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                                                  && VV##1796##k_ == VV##F##7
                                                  && i##aS7##k_ == i##aS7
                                                  && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                  && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb))
                                     && (exists [i##aS7##k_ : int,
                                                 lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                                 VV##1793##k_ : int]
                                           . VV##1793##k_ == VV##F##6
                                             && i##aS7##k_ == i##aS7
                                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                             && (exists [VV##F##5 : int]
                                                   . VV##1793##k_ == VV##F##5
                                                     && i##aS7##k_ == i##aS7
                                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb))
                                     && VV##1802##k_ == VV##F##6
                                     && i##aS7##k_ == i##aS7
                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc))
                     && (exists [lq_anf##7205759403792798200##d1cc##k_ : (Test.State int int),
                                 lq_tmpx##1818##k_ : int,
                                 lq_anf##7205759403792798198##d1ca##k_ : (GHC.Internal.Base.Monad (Test.State int)),
                                 lq_tmpx##1817##k_ : int,
                                 VV##1815##k_ : int,
                                 lq_anf##7205759403792798199##d1cb##k_ : (Test.State int Tuple0),
                                 i##aS7##k_ : int]
                           . VV##1815##k_ == VV##F##13
                             && i##aS7##k_ == i##aS7
                             && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                             && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                             && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                             && lq_tmpx##1817##k_ == w2
                             && lq_tmpx##1818##k_ == x
                             && (exists [VV##F##8 : int,
                                         lq_tmpx##1817 : int,
                                         lq_tmpx##1818 : int,
                                         lq_tmpdb##47 : int,
                                         lq_tmpdb##48 : int]
                                   . lq_tmpx##1818 == VV##F##8
                                     && VV##F##8 == lq_tmpx##1817
                                     && VV##1815##k_ == VV##F##8
                                     && i##aS7##k_ == i##aS7
                                     && lq_anf##7205759403792798198##d1ca##k_ == lq_anf##7205759403792798198##d1ca
                                     && lq_anf##7205759403792798199##d1cb##k_ == lq_anf##7205759403792798199##d1cb
                                     && lq_anf##7205759403792798200##d1cc##k_ == lq_anf##7205759403792798200##d1cc
                                     && lq_tmpx##1817##k_ == lq_tmpx##1817
                                     && lq_tmpx##1818##k_ == lq_tmpx##1818)))
        """
    }
 where
  fixtureSort = doParse'' True sortP "large simplification declarations"
