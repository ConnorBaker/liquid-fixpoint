{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module RootSortCheckTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad.Reader (runReader)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Maybe (isNothing)
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import qualified Language.Fixpoint.Types.Solutions as Sol
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

-- Root and child contexts share immutable inventories without sharing judgments.
tests :: TestTree
tests =
    testGroup
        "root native sort-check preparation"
        [ testGroup
            "whole declaration environments preserve complete diagnostics"
            [ testCase (label ++ "/lowerSets=" ++ show lowerSets) $ do
                let flags = Config.ElabFlags lowerSets False
                    shared = runReader (C.prepareSortCheck (Just native) mempty) flags
                    actual = fmap show (C.checkSortAt (C.extendSortCheck environment shared) F.dummySpan expected candidate)
                    reference = fmap show (C.checkSortAt (runReader (C.prepareSortCheck (Just native) environment) flags) F.dummySpan expected candidate)
                evaluate (force actual) >>= (@?= reference)
                isNothing actual @?= valid
            | (label, environment, expected, candidate, valid) <- judgments
            , lowerSets <- [False, True]
            ]
        , testCase "success and failure alternate with fresh equations and supplies" $ do
            let flags = Config.ElabFlags True False
                shared = runReader (C.prepareSortCheck (Just native) mempty) flags
                environment = F.fromListSEnv [("x", F.FVar 9), ("f", scheme), ("unused", F.FAbs 0 F.FInt)]
                bad = refinement F.FInt (F.PAnd [F.PAtom F.Ueq (F.EVar "x") zero, equal (F.EVar "x") F.PTrue])
                good = refinement F.FInt (equal (F.EVar "x") zero)
                fresh = refinement F.FInt freshBoolean
                candidates = [bad, good, fresh, bad, fresh, good]
                actual = [fmap show (C.checkSortAt (C.extendSortCheck environment shared) F.dummySpan Nothing candidate) | candidate <- candidates]
                reference = [fmap show (runReader (C.checkSorted (Just native) F.dummySpan environment candidate) flags) | candidate <- candidates]
            evaluate (force actual) >>= (@?= reference)
            map isNothing actual @?= [False, True, True, False, True, True]
        , testCase "whole declaration environment retains its outer demand for empty candidates" $ do
            let flags = Config.ElabFlags False False
                environment = error "whole declaration environment forced" :: F.SEnv F.Sort
                shared = runReader (C.prepareSortCheck (Just mempty) mempty) flags
                original = runReader (C.prepareSortCheck (Just mempty) environment) flags
                moved = environment `seq` C.extendSortCheck environment shared
                observe checker = do
                    result <- try (evaluate (checker `seq` ([] :: [F.SortedReft]))) :: IO (Either SomeException [F.SortedReft])
                    pure (either (const True) (const False) result)
            observe original >>= (@?= True)
            observe moved >>= (@?= True)
        , testCase "whole declaration demand leaves unused sort fields lazy" $ do
            let flags = Config.ElabFlags False False
                environment = F.fromListSEnv [("unused", F.FTC (F.symbolNumInfoFTyCon "unused" (error "unused numeric metadata forced") (error "unused fractional metadata forced")))]
                shared = runReader (C.prepareSortCheck (Just mempty) mempty) flags
                candidate = refinement F.FInt F.PTrue
                actual = environment `seq` fmap show (C.checkSortAt (C.extendSortCheck environment shared) F.dummySpan Nothing candidate)
                reference = fmap show (runReader (C.checkSorted (Just mempty) F.dummySpan environment candidate) flags)
            evaluate (force actual) >>= (@?= reference)
            actual @?= Nothing
        , testCase "ground check leaves an unused child environment lazy" $ do
            let root = runReader (C.prepareSortCheck Nothing mempty) (Config.ElabFlags False False)
                child = C.extendSortCheck (error "unused local environment forced") root
                actual = fmap show (C.checkSortAt child F.dummySpan Nothing (refinement F.FInt F.PTrue))
            evaluate (force actual) >>= (@?= Nothing)
        , testCase "local declarations are demanded only by consumed qualifier judgments" $ do
            let (binding, bindings) = F.insertBindEnv "unused" (error "unused declaration metadata forced") () mempty
                kvar = F.KV "empty-domain"
                information qualifiers = mempty{F.bs = bindings, F.quals = qualifiers, F.ws = M.singleton kvar (F.WfC (F.fromListIBindEnv [binding]) ("value", F.FInt, kvar) ())} :: F.SInfo ()
                actual qualifiers = sum (map (length . Sol.qbExprs) (M.elems (Solution.init Config.defConfig (information qualifiers) (S.singleton kvar))))
                ground = F.Q "ground" [F.QP "value" F.PatNone F.FInt] F.PTrue (F.dummyPos "root context demand")
            evaluate (actual []) >>= (@?= 0)
            observed <- try (evaluate (actual [ground])) :: IO (Either SomeException Int)
            either (const True) (const False) observed @?= True
        , testGroup
            "ground checks preserve unused native metadata laziness"
            [ testCase label $ do
                let flags = Config.ElabFlags False False
                    shared = runReader (C.prepareSortCheck (Just environment) mempty) flags
                    candidate = refinement F.FInt F.PTrue
                    actual = fmap show (C.checkSortAt shared F.dummySpan Nothing candidate)
                    reference = fmap show (runReader (C.checkSorted (Just environment) F.dummySpan mempty candidate) flags)
                evaluate (force actual) >>= (@?= reference)
                actual @?= Nothing
            | (label, environment) <-
                [ ("whole native environment", error "unused native environment forced")
                , ("native declarations", mempty{F.seSort = error "unused native declarations forced"})
                , ("native theory", mempty{F.seTheory = error "unused native theory forced"})
                , ("native datatypes", mempty{F.seData = error "unused native datatypes forced"})
                , ("native literals", mempty{F.seLits = error "unused native literals forced"})
                ]
            ]
        ]
  where
    native = mempty{F.seSort = F.fromListSEnv [("nativeUnused", F.FAbs 0 (F.FAbs 1 F.FInt)), ("nativeFree", F.FVar 2)]}

judgments :: [(String, F.SEnv F.Sort, Maybe F.Sort, F.SortedReft, Bool)]
judgments =
    [ ("literal", mempty, Nothing, refinement F.FInt F.PTrue, True)
    , ("complete missing-symbol diagnostic", mempty, Nothing, refinement F.FInt (equal (F.EVar "missing") zero), False)
    , ("nominal Boolean alias mismatch", declarations [("A", F.boolSort), ("B", F.boolSort), ("x", F.FObj "A"), ("y", F.FObj "B")], Nothing, refinement F.FInt (equal (F.EVar "x") (F.EVar "y")), False)
    , ("fractional authority survives numeric binder", declarations [("alpha", F.FFrac), ("x", F.FObj "alpha")], Nothing, F.RR F.FNum (F.Reft ("alpha", modulo)), False)
    , ("numeric authority survives fractional binder", declarations [("alpha", F.FNum), ("x", F.FObj "alpha")], Nothing, F.RR F.FFrac (F.Reft ("alpha", modulo)), True)
    , ("unused forall labels avoid fresh collisions", declarations [("f", scheme), ("unused", F.FAbs 3 (F.FAbs 4 F.FInt)), ("local", F.FVar 5)], Just (F.FAbs 6 F.FInt), refinement F.FInt (F.PAnd [freshBoolean, equal (F.EVar "local") zero]), True)
    , ("whole environment keeps local shadowing", declarations [("x", F.boolSort)] <> declarations [("x", F.FInt)], Nothing, refinement F.FInt (equal (F.EVar "x") zero), False)
    ]
  where
    declarations = F.fromListSEnv
    modulo = equal (F.EBin F.Mod (F.EVar "x") (F.ECon (F.I 2))) zero

refinement :: F.Sort -> F.Expr -> F.SortedReft
refinement source predicate = F.RR source (F.Reft ("value", predicate))

zero :: F.Expr
zero = F.ECon (F.I 0)

equal :: F.Expr -> F.Expr -> F.Expr
equal = F.PAtom F.Eq

scheme :: F.Sort
scheme = F.FAbs 42 (F.FFunc F.FInt (F.FVar 42))

freshBoolean :: F.Expr
freshBoolean = equal (F.EApp (F.EVar "f") zero) F.PTrue
