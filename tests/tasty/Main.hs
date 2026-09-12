{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified ParserTests
import qualified PolyValueTests
import qualified ShareMapTests
import qualified SortCheckTests
import qualified SimplifyTests
import qualified SimplifyKVarTests
import qualified InterpretTests
import qualified UndoANFTests
import Test.Tasty

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ ParserTests.tests
  , PolyValueTests.tests
  , ShareMapTests.tests
  , SortCheckTests.tests
  , SimplifyTests.tests
  , SimplifyKVarTests.tests
  , InterpretTests.tests
  , UndoANFTests.tests
  ]
