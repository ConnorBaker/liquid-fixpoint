module SimplifyTests (tests) where

import Arbitrary (subexprs)
import qualified Language.Fixpoint.Smt.Interface as SMT
import Language.Fixpoint.Solver.Simplify (applyConstantFolding)
import Language.Fixpoint.Types.Config (defConfig)
import Language.Fixpoint.Types.Refinements (Bop (Minus, Mod), Brel (Eq), Constant (I), Expr, ExprBV (..))
import qualified SimplifyInterpreter
import qualified SimplifyPLE
import Test.Tasty (
    TestTree,
    localOption,
    testGroup,
 )
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck (
    NonZero (..),
    Property,
    QuickCheckMaxSize (..),
    QuickCheckTests (..),
    counterexample,
    label,
    testProperty,
 )

tests :: TestTree
tests =
    withOptions $
        testGroup
            "simplification"
            [ testGroup
                "does not increase expression size"
                [ testProperty "PLE" (prop_no_increase SimplifyPLE.simplify')
                , testProperty "Interpreter" (prop_no_increase SimplifyInterpreter.simplify')
                ]
            , moduloTests
            ]
  where
    withOptions tests' = localOption (QuickCheckMaxSize 4) (localOption (QuickCheckTests 500) tests')

integer :: Integer -> Expr
integer = ECon . I

modulo :: Integer -> Integer -> Expr
modulo x y = EBin Mod (integer x) (integer y)

-- Integer arithmetic deliberately exceeds any machine-word range here.
largeInteger :: Integer
largeInteger = 10 ^ (100 :: Int)

moduloCases :: [(Integer, Integer, Integer)]
moduloCases =
    [ (5, 3, 2)
    , (-5, 3, 1)
    , (5, -3, 2)
    , (-5, -3, 1)
    , (0, 3, 0)
    , (0, -3, 0)
    , (6, 3, 0)
    , (-6, 3, 0)
    , (6, -3, 0)
    , (-6, -3, 0)
    , (5, 1, 0)
    , (-5, 1, 0)
    , (5, -1, 0)
    , (-5, -1, 0)
    , (largeInteger + 5, -largeInteger, 5)
    , (-largeInteger - 5, -largeInteger, largeInteger - 5)
    , (-2 * largeInteger, -largeInteger, 0)
    ]

moduloTests :: TestTree
moduloTests =
    testGroup
        "Euclidean modulo"
        [ testGroup
            name
            [ testCase "all signs and unbounded integers" $
                mapM_ (\(x, y, expected) -> simplify (modulo x y) @?= integer expected) moduloCases
            , testCase "zero divisor remains symbolic" $
                mapM_ (\x -> simplify (modulo x 0) @?= modulo x 0) [-largeInteger, -1, 0, 1, largeInteger]
            , testProperty "nonnegative bounded congruent remainder" $ \x (NonZero y) ->
                let result = simplify (modulo x y)
                 in counterexample (show (x, y, result)) $ case result of
                        ECon (I r) -> 0 <= r && r < abs y && (x - r) `rem` y == 0
                        _ -> False
            ]
        | (name, simplify) <-
            [ ("shared constant folding", foldModulo)
            , ("PLE", SimplifyPLE.simplify')
            , ("Interpreter simplification", SimplifyInterpreter.simplify')
            , ("Interpreter evaluation", SimplifyInterpreter.interpret')
            ]
        ]
        `withSmtAgreement` testCase
            "folded constants agree with SMT-LIB mod"
            ( do
                verdicts <-
                    SMT.checkValids
                        defConfig
                        "simplify-mod"
                        []
                        [ PAtom Eq (modulo x y) (foldModulo (modulo x y))
                        | (x, y, _) <- moduloCases
                        ]
                verdicts @?= replicate (length moduloCases) True
            )
  where
    withSmtAgreement paths agreement = testGroup "modulo semantics" [paths, agreement]
    foldModulo (EBin Mod x y) = applyConstantFolding Mod x y
    foldModulo e = e

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
