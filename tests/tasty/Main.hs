{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified ArrayConstantTests
import qualified ClosureLiftingTests
import qualified ConfiguredStringTests
import qualified EliminatedSharingTests
import qualified EtaFreshnessTests
import qualified InterpretTests
import qualified ModelFilterTests
import qualified NativeCallableTests
import qualified NestedKVarActualTests
import qualified PLEAuthorityTests
import qualified ParserTests
import qualified PolyFamilyTests
import qualified QueryAuthorityTests
import qualified RootSortCheckTests
import qualified ScopedSubstitutionTests
import qualified ShareMapTests
import qualified SimplifyKVarTests
import qualified SimplifyTests
import qualified SmtScopeTests
import qualified SolutionPresentationTests
import qualified SortInventoryTests
import qualified SortJudgmentTests
import Test.Tasty
import qualified UndoANFTests

main :: IO ()
main =
    defaultMain $
        testGroup
            "Tests"
            [ ParserTests.tests
            , ShareMapTests.tests
            , SimplifyTests.tests
            , SimplifyKVarTests.tests
            , SolutionPresentationTests.tests
            , InterpretTests.tests
            , ModelFilterTests.tests
            , UndoANFTests.tests
            , ScopedSubstitutionTests.tests
            , SortInventoryTests.tests
            , SortJudgmentTests.tests
            , SmtScopeTests.tests
            , ConfiguredStringTests.tests
            , EliminatedSharingTests.tests
            , ClosureLiftingTests.tests
            , ArrayConstantTests.tests
            , NativeCallableTests.tests
            , NestedKVarActualTests.tests
            , PLEAuthorityTests.tests
            , PolyFamilyTests.tests
            , QueryAuthorityTests.tests
            , RootSortCheckTests.tests
            , EtaFreshnessTests.tests
            ]
