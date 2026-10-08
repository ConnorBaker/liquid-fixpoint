{-# LANGUAGE OverloadedStrings #-}

module SolutionPresentationTests (tests) where

import qualified Data.ByteString.Char8 as Bytes
import Data.Char (isSpace)
import qualified Data.HashMap.Strict as M
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Utils.Files as Files
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import qualified Text.PrettyPrint.HughesPJ as PJ

tests :: TestTree
tests =
    testGroup
        "solution presentation"
        [ testCase "saved cuts and delayed closures retain every scoped token" $ do
            let variable = F.KV "presentation"
                body = closure 4
                formals = [F.Formal "source" "canonical" F.FInt]
                result = F.Result (F.Safe mempty) (M.singleton variable body) (M.singleton variable (F.Delayed body)) (M.singleton variable formals) :: F.Result ()
                entry = PJ.render (PJ.hsep [F.pprint variable PJ.<> F.pprint [("canonical" :: F.Symbol, F.FInt)], PJ.text ":=", F.pprint body])
                expected = "Solution:" ++ entry ++ "Non-cut kvars:" ++ entry
            save result $ \output ->
                filter (not . isSpace) (Bytes.unpack output) @?= filter (not . isSpace) expected
        , testCase "saved lexical sharing has a linear wire bound" $ do
            let saved depth = F.Result (F.Safe mempty) mempty (M.singleton (F.KV "presentation") (F.Delayed (closure depth))) mempty :: F.Result ()
            save (saved 64) $ \small ->
                save (saved 256) $ \large -> do
                    assertBool "padding must not dominate lexical definitions" (Bytes.length large < 256 * 300)
                    assertBool "four times the definitions must not square the wire size" (Bytes.length large < 5 * Bytes.length small)
        ]

save :: F.Result () -> (Bytes.ByteString -> IO ()) -> IO ()
save result observe = withSystemTempDirectory "solution-presentation" $ \directory -> do
    let source = directory </> "Presentation.hs"
    Solution.saveSolution C.defConfig{C.save = True, C.srcFile = source} "" result
    Bytes.readFile (Files.tempFileName (source ++ ".fqout")) >>= observe

closure :: Int -> F.Expr
closure depth = foldr define (F.EApp (F.EVar (name (depth - 1))) (F.ECon (F.I 1))) [0 .. depth - 1]
  where
    name index = F.symbol ("shared_predicate_" ++ show index)
    define index continuation =
        let argument = F.symbol ("argument_" ++ show index)
            witness = F.symbol ("witness_" ++ show index)
            previous = if index == 0 then F.PAtom F.Eq (F.EVar argument) (F.ECon (F.I 1)) else F.EApp (F.EVar (name (index - 1))) (F.EVar argument)
            body = F.PExist [(witness, F.FInt)] (F.PAnd [F.PAtom F.Eq (F.EVar witness) (F.EVar argument), previous])
         in F.ELet (name index) (F.ELam (argument, F.FInt) body) continuation
