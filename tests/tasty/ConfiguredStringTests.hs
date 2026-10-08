{-# LANGUAGE OverloadedStrings #-}

module ConfiguredStringTests (tests) where

import qualified Data.Text as Text
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.SortCheck as So
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Types.Visitor as V
import NativeCallableTests (withSMT)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "configured string operation denotation"
        [ testGroup
            "native laws and raw false laws"
            [ testCase label $ check cfg label expectedUnsat (F.PNot (form name (literal x) (literal y)))
            | (name, trueArguments, falseArguments) <- comparisons
            , (formName, form) <- forms
            , (oracleName, (x, y), expectedUnsat) <- [("true", trueArguments, True), ("false", falseArguments, False)]
            , let cfg = configuration False
                  label = Text.unpack (F.symbolText name) ++ "-" ++ formName ++ "-" ++ oracleName
            ]
        , testGroup
            "abstract mode adds neither truth nor falsity"
            [ testCase label $ check (configuration True) label False (if polarity then atom else F.PNot atom)
            | (name, (x, y), _) <- comparisons
            , (formName, form) <- forms
            , polarity <- [False, True]
            , let atom = form name (literal x) (literal y)
                  label = "abstract-" ++ Text.unpack (F.symbolText name) ++ "-" ++ formName ++ "-" ++ show polarity
            ]
        , testGroup
            "direct and represented operations agree in both modes"
            [ testCase label $ check (configuration abstract) label True (F.PNot (F.PIff (direct name (literal x) (literal y)) (form name (literal x) (literal y))))
            | abstract <- [False, True]
            , (name, (x, y), _) <- comparisons
            , (formName, form) <- drop 1 forms
            , let label = "agreement-" ++ show abstract ++ "-" ++ Text.unpack (F.symbolText name) ++ "-" ++ formName
            ]
        , testGroup
            "concat aliases select the same configured operation"
            [ testCase label $ check (configuration abstract) label True (F.PAtom F.Ne (direct "concatString" (literal "a") (literal "b")) (form "strConcat" (literal "a") (literal "b")))
            | abstract <- [False, True]
            , (formName, form) <- forms
            , let label = "concat-alias-" ++ show abstract ++ "-" ++ formName
            ]
        , testGroup
            "native concatenation facts are not invented in abstract mode"
            [ testCase label $ check (configuration abstract) label (not abstract) (F.PAtom F.Ne (form "strConcat" (literal "a") (literal "b")) (literal "ab"))
            | abstract <- [False, True]
            , (formName, form) <- forms
            , let label = "concat-fact-" ++ show abstract ++ "-" ++ formName
            ]
        , testGroup
            "universal configured application correspondence"
            [ testCase label $
                check
                    (configuration abstract)
                    label
                    True
                    ( F.PExist
                        [("x", F.strSort), ("y", F.strSort)]
                        (F.PNot (F.PIff (direct name (F.EVar "x") (F.EVar "y")) (form name (F.EVar "x") (F.EVar "y"))))
                    )
            | abstract <- [False, True]
            , (name, _, _) <- comparisons
            , (formName, form) <- drop 1 forms
            , let label = "universal-agreement-" ++ show abstract ++ "-" ++ Text.unpack (F.symbolText name) ++ "-" ++ formName
            ]
        ]

comparisons :: [(F.Symbol, (Text.Text, Text.Text), (Text.Text, Text.Text))]
comparisons =
    [ ("strPrefixOf", ("a", "abc"), ("z", "abc"))
    , ("strSuffixOf", ("c", "abc"), ("z", "abc"))
    , ("strContains", ("abc", "b"), ("abc", "z"))
    ]

forms :: [(String, F.Symbol -> F.Expr -> F.Expr -> F.Expr)]
forms =
    [ ("direct", direct)
    , ("whole-value", \name x y -> F.ELet "function" (F.EVar name) (direct "function" x y))
    , ("partial-value", \name x y -> F.ELet "partial" (F.EApp (F.EVar name) x) (F.EApp (F.EVar "partial") y))
    ]

direct :: F.Symbol -> F.Expr -> F.Expr -> F.Expr
direct name x y = F.eApps (F.EVar name) [x, y]

literal :: Text.Text -> F.Expr
literal = F.ESym . F.SL

configuration :: Bool -> FC.Config
configuration abstract = FC.defConfig{FC.allowHO = True, FC.noStringTheory = abstract}

check :: FC.Config -> String -> Bool -> F.Expr -> Assertion
check cfg label expectedUnsat expression = do
    So.checkSortExpr Nothing F.dummySpan names expression @?= Just F.boolSort
    response <-
        withSMT
            (SMT.makeContextWithSEnv cfg ("configured-strings-" ++ label) environment mempty)
            (SMT.smtAssert elaborated >> SMT.command SMT.CheckSat)
    if expectedUnsat
        then response @?= SMT.Unsat
        else response @?= SMT.Sat
  where
    theory = So.theoryEnv cfg (mempty :: F.SInfo ())
    literals = F.fromListSEnv [(F.symbol value, F.strSort) | value <- V.symConsts expression]
    names = literals <> (F.tsSort <$> theory)
    environment = F.symEnv cfg names theory [] literals
    elaborated = So.elaborate (So.ElabParam (FC.solverFlags cfg) "configured string operation" environment) expression
