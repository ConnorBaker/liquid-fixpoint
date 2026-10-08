{-# LANGUAGE OverloadedStrings #-}

module SimplifyTests (tests) where

import Arbitrary (subexprs)
import Language.Fixpoint.Types.Refinements (Bop (Minus, Mod), Brel (Eq), Constant (I), Expr, ExprBV (..))
import Language.Fixpoint.Types.Sorts (Sort (FInt))
import qualified SimplifyInterpreter
import qualified SimplifyPLE
import Test.Tasty (
    TestTree,
    localOption,
    testGroup,
 )
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)
import Test.Tasty.QuickCheck (
    Property,
    QuickCheckMaxSize (..),
    QuickCheckTests (..),
    counterexample,
    label,
    testProperty,
 )

tests :: TestTree
tests =
    testGroup
        "simplification"
        [ withOptions $
            testGroup
                "simplify does not increase expression size"
                [ testProperty "PLE" (prop_no_increase SimplifyPLE.simplify')
                , testProperty "Interpreter" (prop_no_increase SimplifyInterpreter.simplify')
                ]
        , moduloTests
        , testGroup
            "constant substitution respects lexical binding"
            [ testCase name $ assertBool "capture-avoiding substitution" (expected (reduce expression))
            | (name, expression, expected) <-
                [ ("free occurrence", x, (== zero))
                , ("lambda shadow", ELam ("x", FInt) x, isIdentity)
                , ("quantifier shadow", PAll [("x", FInt)] (PAtom Eq x (EVar "y")), isBoundEquality)
                , ("let RHS is outside its binder", ELet "x" x x, isIdentityLet)
                , ("nested lambda shadow", ELam ("y", FInt) (ELam ("x", FInt) x), isNestedIdentity)
                ]
            ]
        ]
  where
    x = EVar "x"
    zero = ECon (I 0)
    reduce = SimplifyPLE.simplifyWithConstants [(x, zero)]
    isIdentity (ELam (binder, FInt) (EVar occurrence)) = binder == occurrence
    isIdentity _ = False
    isBoundEquality (PAll [(binder, FInt)] (PAtom Eq (EVar occurrence) (EVar "y"))) = binder == occurrence
    isBoundEquality _ = False
    isIdentityLet (ELet binder initializer (EVar occurrence)) = initializer == zero && binder == occurrence
    isIdentityLet _ = False
    isNestedIdentity (ELam (_, FInt) body) = isIdentity body
    isNestedIdentity _ = False
    withOptions tests' = localOption (QuickCheckMaxSize 4) (localOption (QuickCheckTests 500) tests')

prop_no_increase :: (Expr -> Expr) -> Expr -> Property
prop_no_increase f e =
    let originalSize = exprSize e
        simplified = f e
        simplifiedSize = exprSize simplified
     in label ("reduced size by " ++ show (originalSize - simplifiedSize)) $
            counterexample
                ( unlines
                    [ show simplifiedSize ++ " > " ++ show originalSize
                    , "simplified: " ++ show simplified
                    ]
                )
                (simplifiedSize <= originalSize)

exprSize :: Expr -> Int
-- Undo the removal of ENeg in @simplify@ so it does not count as increasing the size of the expression.
exprSize (EBin Minus (ECon (I 0)) e) = exprSize (ENeg e)
exprSize e = 1 + sum (exprSize <$> subexprs e)

-- SMT integer mod has a nonnegative remainder for either divisor sign.
-- Zero is deliberately not folded: SMT leaves division by zero unspecified.
moduloTests :: TestTree
moduloTests =
    testGroup
        "Euclidean modulo"
        [ testGroup engine $
            [ testCase (show numerator ++ " mod " ++ show divisor) $
                assertEqual "SMT remainder" (integer expected) (reduce (modulo numerator divisor))
            | (numerator, divisor, expected) <- [(7, 3, 1), (7, -3, 1), (-7, 3, 2), (-7, -3, 2), (-6, -3, 0)]
            ]
                ++ [ testCase "zero divisor stays uninterpreted" $
                        assertEqual "no invented zero-divisor value" (modulo 7 0) (reduce (modulo 7 0))
                   ]
        | (engine, reduce) <- [("PLE simplifier", SimplifyPLE.simplify'), ("interpreter simplifier", SimplifyInterpreter.simplify'), ("interpreter", SimplifyInterpreter.interpret')]
        ]
  where
    integer = ECon . I
    modulo numerator divisor = EBin Mod (integer numerator) (integer divisor)
