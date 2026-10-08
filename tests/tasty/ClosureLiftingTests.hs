{-# LANGUAGE OverloadedStrings #-}

module ClosureLiftingTests (tests) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM_)
import Control.Monad.State.Lazy (evalState)
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy as Bytes
import qualified Data.HashMap.Strict as M
import EliminatedSharingSupport
import qualified EliminatedSharingTests as Sharing
import Language.Fixpoint.Smt.Serialize ()
import qualified Language.Fixpoint.Smt.Types as SMT
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Sanitize as Sanitize
import qualified Language.Fixpoint.SortCheck as So
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Visitor as V
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
    testGroup
        "lexical function closure lifting"
        [ testCase "deep exported closures remain shared after actual query elaboration" deepExport
        , testCase "distinct arguments still require lexical sharing before beta normalization" distinctCalls
        , testCase "captured lexical witness and shadowed annotation keep ownership" capturedAlias
        , testCase "unknown-dependent authored closures are not fixed definitions" unknownClosure
        , testCase "first-class and partial helper use retains beta meaning" firstClass
        , testCase "lexical witnesses shadow globals without changing helper capture" globalShadow
        , testCase "native names can be captured lexical functions" nativeShadow
        , testCase "whole closure ascription remains a checked judgment" badAscription
        , testCase "body-only free sort coordinates remain reserved" bodySortOwner
        , testCase "a global definition may share its nested term binder's spelling" nestedTermOwner
        , testCase "lifting preserves a sealed type abstraction (not solver support)" sealedTypeOwner
        ]

query :: F.IBindEnv -> F.Expr -> F.Expr -> F.FInfo ()
query environment predicate conclusion =
    mempty
        { F.cm = M.singleton 1 (F.mkSubC environment (refinement predicate) (refinement conclusion) (Just 1) [] ())
        , F.hoInfo = F.cfgHoInfo cfg
        }
  where
    refinement body = F.RR F.boolSort (F.Reft ("value", body))

deepExport :: Assertion
deepExport = do
    measures <- mapM measure [20, 40]
    case measures of
        [(nodes, wire), (nodes', wire')] -> do
            assertBool "post-elaboration AST doubling stays linear" (nodes' < 3 * nodes)
            assertBool "SMT wire doubling stays linear" (wire' < 3 * wire)
        _ -> assertFailure "missing depth measurements"
  where
    measure depth = do
        let body = F.subst1 (Sharing.exportedBody depth (Sharing.diamond depth 0)) (sym "v" depth, var "x")
            original = (query (F.fromListIBindEnv [0]) body (F.EEq (var "x") (int 0))){F.bs = F.bindEnvFromList [binding 0 "x" F.FInt F.PTrue]}
        (parameter, _, prepared, _) <- Solver.simplifyFInfo cfg original
        let F.MkDefinedFuns definitions = F.defns prepared
            predicates = map F.crhs (M.elems (F.cm prepared)) ++ [F.reftPred (F.sr_reft refinement) | (_, (_, refinement, _)) <- F.bindEnvToList (F.bs prepared)]
        length definitions @?= depth + 1
        nodes <- evaluate (sum (map (V.size . F.eqBody) definitions) + sum (map V.size predicates))
        let commands = [SMT.DefineFunc (F.eqName definition) [(name, F.sortSmtSort False (So.epEnv parameter) sort) | (name, sort) <- F.eqArgs definition] (F.sortSmtSort False (So.epEnv parameter) (F.eqSort definition)) (F.eqBody definition) | definition <- definitions]
            builders = evalState (traverse SMT.smt2 commands) (So.epEnv parameter)
        wire <- evaluate (sum (map (Bytes.length . toLazyByteString) builders))
        result <- Solver.solve cfg original
        case F.resStatus result of
            F.Safe _ -> pure ()
            status -> assertFailure ("deep exported relation changed meaning: " ++ show status)
        pure (nodes, wire)

-- Unlike the equality-projected export diamond, these applications cannot
-- deduplicate: each previous function is used at two different arguments.
-- This observes the host normalization boundary, not backend solver complexity.
distinctCalls :: Assertion
distinctCalls = forM_ [20, 40] $ \depth -> do
    let name = sym "step"
        define index rest =
            F.ELet
                (name index)
                ( F.ELam
                    ("argument", F.FInt)
                    ( if index == 0
                        then var "argument"
                        else
                            F.EBin
                                F.Plus
                                (F.EApp (var (name (index - 1))) (var "argument"))
                                (F.EApp (var (name (index - 1))) (F.EBin F.Plus (var "argument") (int 1)))
                    )
                )
                rest
        body = foldr define (F.EEq (F.EApp (var (name depth)) (var "x")) (int 0)) [0 .. depth]
        original = (query (F.fromListIBindEnv [0]) body F.PFalse){F.bs = F.bindEnvFromList [binding 0 "x" F.FInt F.PTrue]}
    (_, _, prepared, _) <- Solver.simplifyFInfo cfg original
    let F.MkDefinedFuns definitions = F.defns prepared
    length definitions @?= depth + 1
    assertBool
        "distinct-call definitions remain linear after actual elaboration"
        (sum (map (V.size . F.eqBody) definitions) < 40 * fromIntegral depth)

capturedAlias :: Assertion
capturedAlias = do
    let body =
            F.PExist
                [("alpha", F.FInt), ("x", F.FObj "alpha")]
                ( F.ELet
                    "helper"
                    (F.ELam ("y", F.FObj "alpha") (F.EEq (var "y") (var "x")))
                    (F.PAnd [F.EEq (var "x") (F.ECon (F.R (1 / 2))), F.EApp (var "helper") (var "x")])
                )
        original = (query (F.fromListIBindEnv [0]) body F.PFalse){F.bs = F.bindEnvFromList [binding 0 "alpha" F.FFrac F.PTrue], F.gLits = F.fromListSEnv [("alpha", F.FFrac)]}
    (_, _, prepared, _) <- Solver.simplifyFInfo cfg original
    let F.MkDefinedFuns definitions = F.defns prepared
    assertBool ("a captured local becomes a definition parameter: " ++ show (map F.eqArgs definitions)) (any ((== [F.FReal, F.FReal]) . map snd . F.eqArgs) definitions)
    result <- Solver.solve cfg original
    case F.resStatus result of
        F.Unsafe _ _ -> pure ()
        status -> assertFailure ("numeric annotation was shadowed by lexical Int: " ++ show status)

unknownClosure :: Assertion
unknownClosure = forM_ [False, True] $ \indirect -> do
    let unknown = F.PKVar (kvar 0) mempty mempty
        helper = F.ELet "helper" (F.ELam ("x", F.FInt) (var (if indirect then "alias" else "flag"))) (F.EApp (var "helper") (int 0))
        body = F.ELet "flag" unknown (if indirect then F.ELet "alias" (var "flag") helper else helper)
        info = mempty{F.bs = F.bindEnvFromList [binding 0 "target" F.boolSort body]}
        F.MkDefinedFuns definitions = F.defns (Sanitize.shareFunctionLets cfg info)
    definitions @?= []

firstClass :: Assertion
firstClass = forM_ [False, True] $ \partial -> do
    let helper = F.ELam ("x", F.FInt) (F.ELam ("y", F.FInt) (F.EBin F.Plus (var "x") (var "y")))
        applied =
            if partial
                then F.ELet "part" (F.EApp (var "helper") (int 1)) (F.EApp (var "part") (int 2))
                else F.EApp (F.ELam ("callback", F.FFunc F.FInt (F.FFunc F.FInt F.FInt)) (F.eApps (var "callback") [int 1, int 2])) (var "helper")
        original = query mempty (F.ELet "helper" helper (F.EEq applied (int 3))) F.PFalse
    result <- Solver.solve cfg original
    case F.resStatus result of
        F.Unsafe _ _ -> pure ()
        status -> assertFailure ("first-class helper lost its definition: " ++ show status)

globalShadow :: Assertion
globalShadow = forM_ [0, 1] $ \value -> do
    let body =
            F.PExist
                [("fixed", F.FInt)]
                ( F.PAnd
                    [ F.EEq (var "fixed") (int 1)
                    , F.ELet "helper" (F.ELam ("arg", F.FInt) (var "fixed")) (F.EEq (F.EApp (var "helper") (int 0)) (int value))
                    ]
                )
        collision = F.tempSymbol "lexical_definition" (0 :: Integer)
        original =
            (query (F.fromListIBindEnv [0]) body F.PFalse)
                { F.gLits = F.fromListSEnv [("fixed", F.FInt), (collision, F.FInt)]
                , F.bs = F.bindEnvFromList [binding 0 "fixed" F.FInt (F.EEq (var "fixed") (int 0))]
                }
    (_, _, prepared, _) <- Solver.simplifyFInfo cfg original
    let F.MkDefinedFuns definitions = F.defns prepared
    assertBool "lexical fixed is a typed capture, not a free global" (any ((== [F.FInt, F.FInt]) . map snd . F.eqArgs) definitions)
    assertBool "fresh helper avoids a reserved future-style name" (all ((/= collision) . F.eqName) definitions)
    result <- Solver.solve cfg original
    case (value, F.resStatus result) of
        (0, F.Safe _) -> pure ()
        (1, F.Unsafe _ _) -> pure ()
        _ -> assertFailure ("global shadow changed lexical relation: " ++ show (F.resStatus result))

nativeShadow :: Assertion
nativeShadow = forM_ [0, 1] $ \value -> do
    let callback = F.FFunc F.boolSort F.FInt
        body =
            F.PExist
                [("bool_to_int", callback)]
                ( F.PAnd
                    [ F.EEq (F.EApp (var "bool_to_int") F.PTrue) (int 1)
                    , F.ELet
                        "helper"
                        (F.ELam ("arg", F.boolSort) (F.EApp (var "bool_to_int") (var "arg")))
                        (F.EEq (F.EApp (var "helper") F.PTrue) (int value))
                    ]
                )
    result <- Solver.solve cfg (query mempty body F.PFalse)
    case (value, F.resStatus result) of
        (0, F.Safe _) -> pure ()
        (1, F.Unsafe _ _) -> pure ()
        _ -> assertFailure ("native name escaped its lexical capture: " ++ show (F.resStatus result))

badAscription :: Assertion
badAscription = do
    let invalid = F.ECst (F.ELam ("x", F.FInt) (var "x")) (F.FFunc F.boolSort F.boolSort)
        body = F.ELet "helper" invalid (F.EEq (F.EApp (var "helper") (int 0)) (int 0))
        info = mempty{F.bs = F.bindEnvFromList [binding 0 "target" F.boolSort body]}
        F.MkDefinedFuns definitions = F.defns (Sanitize.shareFunctionLets cfg info)
    outcome <- try (evaluate (sum (map (V.size . F.eqBody) definitions))) :: IO (Either SomeException Integer)
    case outcome of
        Left _ -> pure ()
        Right _ -> assertFailure "lifting erased an incompatible whole-lambda ascription"

bodySortOwner :: Assertion
bodySortOwner = do
    let collision = F.tempSymbol "lexical_definition" (0 :: Integer)
        sort = F.FObj collision
        literal = F.ECon (F.L "0" sort)
        body = F.ELet "helper" (F.ELam ("x", sort) (var "x")) (F.EEq (F.EApp (var "helper") literal) literal)
        info = mempty{F.bs = F.bindEnvFromList [binding 0 "target" F.boolSort body]}
        F.MkDefinedFuns definitions = F.defns (Sanitize.shareFunctionLets cfg info)
    length definitions @?= 1
    assertBool "free FObj inside a body is not a generated declaration owner" (all ((/= collision) . F.eqName) definitions)

nestedTermOwner :: Assertion
nestedTermOwner = forM_ [0, 1] $ \value -> do
    let collision = F.tempSymbol "lexical_definition" (0 :: Integer)
        helper = F.ELam ("argument", F.FInt) (F.PAll [(collision, F.FInt)] (F.PImp (F.EEq (var collision) (int 0)) (F.EEq (var "argument") (int 0))))
        original = query mempty (F.ELet "helper" helper (F.EApp (var "helper") (int value))) F.PFalse
    (_, _, prepared, _) <- Solver.simplifyFInfo cfg original
    let F.MkDefinedFuns definitions = F.defns prepared
    assertBool "the actual global owner collides with its nested binder" (any ((== collision) . F.eqName) definitions)
    result <- Solver.solve cfg original
    case (value, F.resStatus result) of
        (0, F.Unsafe _ _) -> pure ()
        (1, F.Safe _) -> pure ()
        _ -> assertFailure ("nested lexical owner changed relation: " ++ show (F.resStatus result))

-- ETAbs is not currently accepted by SortCheck. This checks only the lifting
-- pass's existing sealed-subtree boundary, not successful source verification.
sealedTypeOwner :: Assertion
sealedTypeOwner = do
    let collision = F.tempSymbol "lexical_definition" (0 :: Integer)
        sealed = F.ETAbs (F.ELet "hidden" (F.ELam ("x", F.FObj collision) (var "x")) (var "hidden")) collision
        body = F.PAnd [F.ELet "helper" (F.ELam ("x", F.FInt) (F.EEq (var "x") (int 0))) (F.EApp (var "helper") (int 0)), sealed]
        info = mempty{F.bs = F.bindEnvFromList [binding 0 "target" F.boolSort body]}
        prepared = Sanitize.shareFunctionLets cfg info
        F.MkDefinedFuns definitions = F.defns prepared
        (_, refinement, _) = F.lookupBindEnv 0 (F.bs prepared)
    length definitions @?= 1
    case F.reftPred (F.sr_reft refinement) of
        F.PAnd [_, retained] -> retained @?= sealed
        _ -> assertFailure "lifting changed the sealed subtree's enclosing syntax"
