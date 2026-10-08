{-# LANGUAGE OverloadedStrings #-}

module UndoANFTests(tests) where

import Language.Fixpoint.Types (SortedReft(..), Symbol,
                                isPrefixOfSym, anfPrefix, syms)
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Solver.EnvironmentReduction (undoANFSimplifyingWith)
import Arbitrary
import qualified Data.HashMap.Strict as M
import Test.Tasty (TestTree, testGroup, adjustOption)
import Test.Tasty.HUnit ((@?=))
import qualified Test.Tasty.HUnit as H
import Test.Tasty.QuickCheck ((===))
import qualified Test.Tasty.QuickCheck as Q


tests :: TestTree
tests =
  withOptions $
    testGroup
      "undoANFSimplifyingWith id id"
      [ H.testCase "id on empty env" $
          simpleUndoANF [] @?= M.empty
      , H.testCase "self-cycle in a KVar actual preserves the binding" $
          let bindings =
                [
                  ( "lq_anf$x"
                  , sorted
                      "v"
                      ( F.PAnd
                          [ F.EEq (F.EVar "v") (F.EVar "input")
                          , F.PKVar
                              (F.KV "k")
                              mempty
                              (F.toKVarSubst (M.singleton "actual" (F.EVar "lq_anf$x")))
                          ]
                      )
                  )
                ]
           in simpleUndoANF bindings @?= M.fromList bindings
      , H.testCase "reciprocal aliases preserve both equalities" $
          let bindings =
                [ ("lq_anf$x", equalTo (F.EVar "lq_anf$y"))
                , ("lq_anf$y", equalTo (F.EVar "lq_anf$x"))
                ]
           in simpleUndoANF bindings @?= M.fromList bindings
      , H.testCase "acyclic chains still inline" $
          simpleUndoANF
            [ ("lq_anf$x", equalTo (F.expr (1 :: Integer)))
            , ("lq_anf$y", equalTo (F.EVar "lq_anf$x"))
            , ("output", equalTo (F.EVar "lq_anf$y"))
            ]
            @?= M.fromList
              [ (name, equalTo (F.expr (1 :: Integer)))
              | name <- ["lq_anf$x", "lq_anf$y", "output"]
              ]
      , H.testCase "acyclic prefix into a cycle stops at the cycle" $
          simpleUndoANF
            [ ("lq_anf$x", equalTo (F.EVar "lq_anf$y"))
            , ("lq_anf$y", equalTo (F.EVar "lq_anf$z"))
            , ("lq_anf$z", equalTo (F.EVar "lq_anf$y"))
            , ("output", equalTo (F.EVar "lq_anf$x"))
            ]
            @?= M.fromList
              [ ("lq_anf$x", equalTo (F.EVar "lq_anf$y"))
              , ("lq_anf$y", equalTo (F.EVar "lq_anf$z"))
              , ("lq_anf$z", equalTo (F.EVar "lq_anf$y"))
              , ("output", equalTo (F.EVar "lq_anf$y"))
              ]
      , H.testCase "refinement value binder is not a lookup dependency" $
          let value =
                sorted
                  "lq_anf$x"
                  (F.EEq (F.EVar "lq_anf$x") (F.expr (1 :: Integer)))
           in simpleUndoANF
                [("lq_anf$x", value), ("output", equalTo (F.EVar "lq_anf$x"))]
                @?= M.fromList
                  [("lq_anf$x", value), ("output", equalTo (F.expr (1 :: Integer)))]
      , H.testCase "unselected dependency does not close an inline cycle" $
          simpleUndoANF
            [ ("lq_anf$x", equalTo (F.EVar "plain"))
            , ("plain", equalTo (F.EVar "lq_anf$x"))
            , ("output", equalTo (F.EVar "lq_anf$x"))
            ]
            @?= M.fromList
              [ (name, equalTo (F.EVar "plain"))
              | name <- ["lq_anf$x", "plain", "output"]
              ]
      , H.testCase "shadowed self-reference does not create an inline cycle" $
          let bindings =
                [
                  ( "lq_anf$x"
                  , sorted
                      "v"
                      ( F.PAnd
                          [ F.EEq (F.EVar "v") (F.expr (1 :: Integer))
                          , F.PAll
                              [("lq_anf$x", F.FInt)]
                              (F.EEq (F.EVar "lq_anf$x") (F.EVar "lq_anf$x"))
                          ]
                      )
                  )
                ]
           in simpleUndoANF (bindings ++ [("output", equalTo (F.EVar "lq_anf$x"))])
                @?= M.fromList (bindings ++ [("output", equalTo (F.expr (1 :: Integer)))])
      , testGroup "type wrappers preserve term substitution" $
          [ H.testCase name $
              simpleUndoANF
                [ ("lq_anf$x", equalTo (F.expr (1 :: Integer)))
                , ("output", equalTo (wrap (F.EVar "lq_anf$x")))
                ]
                @?= M.fromList
                  [ ("lq_anf$x", equalTo (F.expr (1 :: Integer)))
                  , ("output", equalTo (wrap (F.expr (1 :: Integer))))
                  ]
          | (name, wrap) <-
              [ ("type application retains its sort", flip F.ETApp (F.FObj "lq_anf$x"))
              , ("type abstraction does not bind the term name", flip F.ETAbs "lq_anf$x")
              ]
          ]
      , H.testCase "inserting an alias cannot capture its free variable" $
          let output =
                simpleUndoANF
                  [ ("lq_anf$x", equalTo (F.EVar "captured"))
                  , ("output", equalTo (F.ELam ("captured", F.FInt) (F.EVar "lq_anf$x")))
                  ]
           in case F.reftPred . F.sr_reft <$> M.lookup "output" output of
                Just (F.PAtom F.Eq _ body@(F.ELam (binder, _) (F.EVar free))) -> do
                  H.assertBool "inserted free name became bound" (binder /= free)
                  F.syms body @?= F.syms (F.EVar "captured" :: F.Expr)
                other -> H.assertFailure (show other)
      , H.testCase "no selected aliases preserve lexical spelling" $
          let bindings = [("output", equalTo (F.PAnd [F.EVar "x", F.ELam ("x", F.FInt) (F.EVar "x")]))]
           in simpleUndoANF bindings @?= M.fromList bindings
      , Q.testProperty "id when env contains no lq_anf$* bindings" $
          prop_no_change (M.fromList . unEnv . unNoAnfEnv) simpleUndoANFNoAnfEnv
      , testGroup
          "zero anf vars left afterwards, starting with:"
          [ Q.testProperty "no anf vars" $
              prop_no_anfs simpleUndoANFNoAnfEnv
          , Q.testProperty "single-level anf vars" $
              prop_no_anfs simpleUndoANFFlatAnfEnv
          , Q.testProperty "chained anf vars" $
              prop_no_anfs simpleUndoANFChainedAnfEnv
          ]
      ]
  where
    withOptions = adjustOption (min (Q.QuickCheckMaxSize 8))   -- adjustOption . min because we don't want to default to the enormous value.
                  . adjustOption (max (Q.QuickCheckTests 500)) -- adjustOption . max because we may want larger on the command line.

-- | 5 seconds (in microseconds).
timeout :: Int
timeout = 5000000

prop_no_change :: (Q.Arbitrary e, Eq e, Show e) => (e -> M.HashMap Symbol SortedReft) -> (e -> M.HashMap Symbol SortedReft) -> e -> Q.Property
prop_no_change toHashMap f e = Q.within timeout $ f e === toHashMap e

prop_no_anfs :: (Q.Arbitrary e, Eq e, Show e) => (e -> M.HashMap Symbol SortedReft) -> e -> Q.Property
prop_no_anfs f e = Q.within timeout . checkNoAnfs . f $ e
  where
    checkNoAnfs m = M.filter (any isAnfVar . syms) m === M.empty
    isAnfVar = isPrefixOfSym anfPrefix

-- | We perform tests with only trivial lenses (i.e. id)
simpleUndoANF :: [(Symbol, SortedReft)] -> M.HashMap Symbol SortedReft
simpleUndoANF = undoANFSimplifyingWith id id . M.fromList

sorted :: Symbol -> F.Expr -> SortedReft
sorted name predicate = F.RR F.FInt (F.Reft (name, predicate))

equalTo :: F.Expr -> SortedReft
equalTo = sorted "v" . F.EEq (F.EVar "v")

----------------------------------------------------
-- | simpleUndoANF conjugated with various newtypes
----------------------------------------------------

simpleUndoANFEnv :: Env -> M.HashMap Symbol SortedReft
simpleUndoANFEnv = simpleUndoANF . unEnv

simpleUndoANFNoAnfEnv :: NoAnfEnv -> M.HashMap Symbol SortedReft
simpleUndoANFNoAnfEnv = simpleUndoANFEnv . unNoAnfEnv

simpleUndoANFFlatAnfEnv :: FlatAnfEnv -> M.HashMap Symbol SortedReft
simpleUndoANFFlatAnfEnv = simpleUndoANFEnv . unFlatAnfEnv

simpleUndoANFChainedAnfEnv :: ChainedAnfEnv -> M.HashMap Symbol SortedReft
simpleUndoANFChainedAnfEnv = simpleUndoANFEnv . unChainedAnfEnv
