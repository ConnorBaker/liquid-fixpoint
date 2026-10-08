{-# LANGUAGE OverloadedStrings #-}

module EtaFreshnessTests (tests) where

import qualified Data.HashMap.Strict as M
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

integer :: Integer -> F.Expr
integer = F.ECon . F.I

lambda :: F.Symbol -> F.Expr -> F.Expr
lambda name = F.ELam (name, F.intSort)

query :: F.Symbol -> F.Expr -> F.Expr -> F.FInfo ()
query global assumption goal =
    F.fi [constraint] [] mempty globals mempty mempty [] mempty True False [] axioms []
  where
    refinement predicate = F.RR F.intSort (F.Reft ("value", predicate))
    constraint = F.mkSubC mempty (refinement assumption) (refinement goal) (Just 1) [] ()
    globals = F.fromListSEnv [(global, F.intSort), ("identity", F.FFunc F.intSort F.intSort), ("g", F.FFunc F.intSort (F.FFunc F.intSort F.intSort))]
    axioms =
        mempty
            { F.aenvExpand = M.singleton 1 True
            , F.aenvEqs = [F.mkEquation "identity" [("argument", F.intSort)] (F.EVar "argument") F.intSort]
            }

examples :: [(String, F.FInfo (), Bool)]
examples =
    [ ("free global / " ++ show (global, valid), query global (F.EEq (F.EVar global) (integer 0)) (F.EEq expression (integer (if valid then 0 else 1))), valid)
    | global <- ["ordinaryGlobal", "eta##0"]
    , valid <- [True, False]
    , let expression = F.eApps (lambda "x" (F.EVar global)) [integer 1]
    ]
        ++ [ ("outer binder / " ++ show (outer, valid), query "ordinaryGlobal" F.PTrue (F.EEq expression (integer (if valid then 1 else 2))), valid)
           | outer <- ["outer", "eta##0"]
           , valid <- [True, False]
           , let expression = F.eApps (lambda outer (lambda "y" (F.EVar outer))) [integer 1, integer 2]
           ]
        ++ [ ("shadowed global / " ++ show (binder, valid), query binder (F.EEq (F.EVar binder) (integer 0)) (F.EEq expression (integer (if valid then 1 else 0))), valid)
           | binder <- ["ordinaryGlobal", "etaSource"]
           , valid <- [True, False]
           , let expression = F.eApps (lambda binder (F.EIte (F.EEq (F.EVar binder) (integer 0)) (integer 0) (integer 1))) [integer 1]
           ]
        ++ [ (label ++ " / " ++ show (binder, valid), query "ordinaryGlobal" F.PTrue (F.EEq expression (integer (if valid then correct else wrong))), valid)
           | binder <- ["ordinary", "eta##0"]
           , (label, expression, correct, wrong) <-
                [ ("nested shadow", F.eApps (lambda binder (lambda binder (F.EVar binder))) [integer 1, integer 2], 2, 1)
                , ("sibling bindings", F.EBin F.Plus (F.eApps (lambda binder (F.EVar binder)) [integer 1]) (F.eApps (lambda binder (F.EBin F.Plus (F.EVar binder) (integer 1))) [integer 1]), 3, 4)
                , ("nested different sorts", F.eApps (lambda binder (F.eApps (F.ELam (binder, F.boolSort) (F.EIte (F.EVar binder) (integer 1) (integer 0))) [F.PTrue])) [integer 2], 1, 0)
                , ("shadowed branch premise", F.eApps (lambda binder (F.EIte (F.EEq (F.EVar binder) (integer 0)) (F.eApps (lambda binder (F.EIte (F.EEq (F.EVar binder) (integer 0)) (integer 0) (integer 1))) [integer 1]) (integer 0))) [integer 0], 1, 0)
                ]
           , valid <- [True, False]
           ]
        ++ [ ("future generated-looking argument / " ++ show valid, query "eta##1" (F.EEq (F.EVar "eta##1") (integer 0)) (F.EEq expression (integer (if valid then 0 else 2))), valid)
           | valid <- [True, False]
           , let expression = F.eApps (lambda "x" (lambda "eta##1" (F.EVar "x"))) [F.EVar "eta##1", integer 2]
           ]
        ++ [ ("eta expansion supplied argument / " ++ show (global, valid), query global F.PTrue (F.EEq partial explicit), valid)
           | global <- ["ordinaryGlobal", "eta##0"]
           , valid <- [True, False]
           , let partial = F.eApps (F.EVar "g") [F.EVar global]
           , let explicit = lambda "x" (F.eApps (F.EVar "g") [F.EVar (if valid then global else "x"), F.EVar "x"])
           ]
        ++ lexicalOwnershipExamples

-- Introduce the colliding lambda through unfolding: normalizing a lambda in
-- the original query can otherwise rename away the ownership discriminator.
lexicalOwnershipExamples :: [(String, F.FInfo (), Bool)]
lexicalOwnershipExamples =
    [ (label ++ " / " ++ show valid, ownedQuery argument body expected, valid)
    | valid <- [True, False]
    , (label, argument, body, expected) <-
        [
            ( "bound measure owner"
            , F.FFunc box F.intSort
            , F.ELam ("choose", F.FFunc box F.intSort) (identity (choose (full zero)))
            , F.ELam ("callback", F.FFunc box F.intSort) (if valid then F.EApp (F.EVar "callback") (full zero) else zero)
            )
        ,
            ( "bound constructor owner"
            , F.FFunc F.intSort box
            , F.ELam ("Full", F.FFunc F.intSort box) (identity (choose (full zero)))
            , F.ELam ("builder", F.FFunc F.intSort box) (if valid then choose (F.EApp (F.EVar "builder") zero) else zero)
            )
        ,
            ( "unfolding cannot capture a free global"
            , F.intSort
            , lambda "sharedGlobal" (F.EApp (F.EVar "reveal") zero)
            , lambda "argument" (if valid then integer 7 else F.EVar "argument")
            )
        ]
    ]
        ++ [ ( "existential generated-name collision / " ++ show valid
             , query global assumption (F.EEq (identity (F.EVar global)) (integer (if valid then 0 else 1)))
             , valid
             )
           | valid <- [True, False]
           , let global = F.existSymbol "x" 0
           , let assumption = F.PExist [("x", F.intSort)] (F.PAnd [F.EEq (F.EVar "x") (integer 1), F.EEq (F.EVar global) zero])
           ]
  where
    zero = integer 0
    identity = F.EApp (F.EVar "identity")
    choose = F.EApp (F.EVar "choose")
    full = F.EApp (F.EVar "Full")
    tycon = F.symbolFTycon (F.dummyLoc "OwnedBox")
    box = F.FTC tycon
    ownedQuery argument body expected =
        base
            { F.gLits =
                F.gLits base
                    <> F.fromListSEnv
                        [ ("Full", F.FFunc F.intSort box)
                        , ("choose", F.FFunc box F.intSort)
                        , ("maker", F.FFunc F.intSort result)
                        , ("reveal", F.FFunc F.intSort F.intSort)
                        ]
            , F.ddecls = [F.DDecl tycon 0 [F.DCtor (F.dummyLoc "Full") [F.DField (F.dummyLoc "payload") F.intSort]]]
            , F.ae =
                (F.ae base)
                    { F.aenvEqs =
                        F.aenvEqs (F.ae base)
                            ++ [ F.mkEquation "maker" [("ignored", F.intSort)] body result
                               , F.mkEquation "reveal" [("ignored", F.intSort)] (F.EVar "sharedGlobal") F.intSort
                               ]
                    , F.aenvSimpl = [F.SMeasure "choose" "Full" ["field"] (F.EVar "field")]
                    }
            }
      where
        result = F.FFunc argument F.intSort
        base = query "sharedGlobal" (F.EEq (F.EVar "sharedGlobal") (integer 7)) (F.EEq (F.EApp (F.EVar "maker") zero) expected)

tests :: TestTree
tests =
    testGroup
        "PLE eta-name alpha equivalence"
        [ testCase (label ++ " / " ++ show solver) $ do
            let config =
                    C.defConfig
                        { C.solver = solver
                        , C.srcFile = "eta-name-audit"
                        , C.cores = Just 1
                        , C.allowHO = True
                        , C.rewriteAxioms = True
                        , C.noEnvReduction = True
                        , C.noslice = True
                        , C.etabeta = True
                        }
            result <- timeout (20 * 1000000) (Solver.solve config original)
            case fmap F.resStatus result of
                Just (F.Safe _) -> assertBool "false eta-name proof became Safe" valid
                Just (F.Unsafe _ failures) -> do
                    assertBool "alpha-equivalent lawful lambda rejected" (not valid)
                    map fst failures @?= [1]
                other -> assertFailure ("no checked verdict: " ++ show other)
        | solver <- [C.Z3, C.Cvc5]
        , (label, original, valid) <- examples
        ]
