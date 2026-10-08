{-# LANGUAGE OverloadedStrings #-}

module NativeCarrierInferenceTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad.Reader (runReader)
import Data.Bifunctor (first)
import Data.Char (isSpace)
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "native carrier inference"
        [ testGroup
            "lowered containers retain variable origins"
            [ testCase (name ++ "/" ++ show relation ++ "/reverse=" ++ show reversed) $
                accepted
                    (Config.ElabFlags True False)
                    [("f", scheme (container (F.FVar 42))), ("y", F.arraySort F.strSort value)]
                    (atom reversed relation (call "f") (F.EVar "y"))
            | (name, container, value) <- [("set", F.setSort, F.boolSort), ("bag", F.bagSort, F.intSort)]
            , relation <- [F.Ueq, F.Une]
            , reversed <- [False, True]
            ]
        , testGroup
            "erased arguments do not constrain shared variables"
            [ testCase (show relation ++ "/phantomFirst=" ++ show phantomFirst ++ "/reverse=" ++ show reversed) $
                accepted
                    (Config.solverFlags Config.defConfig)
                    [("f", scheme (position phantomFirst (opaque (F.FVar 42)) (F.FVar 42))), ("y", position phantomFirst (opaque F.strSort) F.boolSort)]
                    (atom reversed relation (call "f") (F.EVar "y"))
            | relation <- [F.Ueq, F.Une]
            , phantomFirst <- [False, True]
            , reversed <- [False, True]
            ]
        , testGroup
            "numeric scalar compatibility does not select aggregate indices"
            [ testCase (show relation ++ "/reverseOrder=" ++ show reversed) $
                accepted
                    (Config.solverFlags Config.defConfig)
                    [("f", scheme (F.FVar 42)), ("wrap", F.FAbs 43 (F.FFunc (F.FVar 43) (F.arraySort (F.FVar 43) F.intSort))), ("arr", F.arraySort F.intSort F.intSort)]
                    ( F.ELet
                        "v"
                        (call "f")
                        ( F.PAnd
                            ( ordered
                                reversed
                                [ F.PAtom relation (F.EApp (F.EVar "wrap") (F.EVar "v")) (F.EVar "arr")
                                , F.PAtom relation (F.EVar "v") (F.ECon (F.R 0))
                                ]
                            )
                        )
                    )
            | relation <- [F.Ueq, F.Une]
            , reversed <- [False, True]
            ]
        , testGroup
            "equal default carriers still propagate aggregate requirements"
            [ testCase (show relation ++ "/reverseOrder=" ++ show reversed) $
                accepted
                    (Config.solverFlags Config.defConfig)
                    [("f", scheme (F.arraySort (F.FVar 42) F.intSort)), ("g", scheme (F.arraySort (F.FVar 42) F.intSort)), ("arr", F.arraySort F.strSort F.intSort)]
                    ( F.ELet
                        "a"
                        (call "f")
                        ( F.ELet
                            "b"
                            (call "g")
                            ( F.PAnd
                                ( ordered
                                    reversed
                                    [ F.PAtom relation (F.EVar "a") (F.EVar "b")
                                    , F.PAtom relation (F.EVar "a") (F.EVar "arr")
                                    ]
                                )
                            )
                        )
                    )
            | relation <- [F.Ueq, F.Une]
            , reversed <- [False, True]
            ]
        , testGroup
            "deferred scalar links can acquire aggregate carriers"
            [ testCase (show relation ++ "/reverseOrder=" ++ show reversed) $
                accepted
                    (Config.solverFlags Config.defConfig)
                    [("f", scheme (F.FVar 42)), ("g", scheme (F.FVar 42)), ("h", scheme (F.FVar 42)), ("arr", F.arraySort F.strSort F.intSort)]
                    ( F.ELet
                        "a"
                        (call "f")
                        ( F.ELet
                            "b"
                            (call "g")
                            ( F.ELet
                                "c"
                                (call "h")
                                ( F.PAnd
                                    ( ordered
                                        reversed
                                        [ F.PAtom relation (F.EVar "b") (F.EVar "c")
                                        , F.PAtom relation (F.EVar "a") (F.EVar "b")
                                        , F.PAtom relation (F.EVar "a") (F.EVar "arr")
                                        ]
                                    )
                                )
                            )
                        )
                    )
            | relation <- [F.Ueq, F.Une]
            , reversed <- [False, True]
            ]
        , testGroup
            "canonical carrier reconstruction"
            [ testCase label $
                accepted
                    (Config.solverFlags Config.defConfig)
                    [("f", scheme (F.FVar 42)), ("y", source)]
                    (F.PAtom F.Ueq (call "f") (F.EVar "y"))
            | (label, source) <- [("bitvector", F.sizedBitVecSort "Size8"), ("finite field", F.finfieldSort (F.FNatNum 17))]
            ]
        , testCase "native datatype reconstruction retains padded parameters" $ do
            let constructor = F.symbolFTycon (F.dummyLoc "CarrierData")
                declaration = F.DDecl constructor 2 [F.DCtor (F.dummyLoc "CarrierDataValue") []]
                source = F.FApp (F.FTC constructor) F.strSort
                environment =
                    mempty
                        { F.seSort = F.fromListSEnv [("f", scheme (F.FVar 42)), ("y", source)]
                        , F.seData = F.fromListSEnv [("CarrierData", declaration)]
                        }
            F.sortSmtSort False environment source @?= F.SData constructor [F.SString, F.SInt]
            acceptedIn (Config.solverFlags Config.defConfig) environment (F.PAtom F.Ueq (call "f") (F.EVar "y"))
        , testCase "native carrier occurs checking rejects infinite instances" $ do
            let environment = mempty{F.seSort = F.fromListSEnv [("f", scheme (F.FVar 42)), ("wrap", F.FAbs 43 (F.FFunc (F.FVar 43) (F.arraySort (F.FVar 43) F.intSort)))]}
                expression = F.ELet "v" (call "f") (F.PAtom F.Ueq (F.EVar "v") (F.EApp (F.EVar "wrap") (F.EVar "v")))
                parameter = C.ElabParam (Config.solverFlags Config.defConfig) "native occurs control" environment
            result <- evaluate (force (first show (C.elabExprE parameter Nothing expression)))
            assertBool (show result) (either (const True) (const False) result)
        , testGroup
            "default variable projection preserves native translation"
            [ testCase (show lowerSets ++ "/" ++ show source) $ do
                let environment = mempty{F.seSetBag = lowerSets}
                F.sortSmtSortWithVars (const F.SInt) environment source @?= F.sortSmtSort False environment source
            | lowerSets <- [False, True]
            , source <- [F.FVar 9, F.setSort (F.FVar 9), F.bagSort (F.FVar 9), F.FFunc (F.FVar 9) F.strSort, opaque (F.FVar 9), F.FAbs 3 (F.arraySort (F.FVar 2) (F.FAbs 7 (F.FVar 6)))]
            ]
        , testCase "declaration projection retains enclosing nested abstraction threshold" $ do
            let source = F.FAbs 3 (F.arraySort (F.FVar 2) (F.FAbs 7 (F.arraySort (F.FVar 6) (F.FVar 7))))
            F.sortSmtSort True mempty source @?= F.SArray (F.SVar 2) (F.SArray (F.SVar 6) F.SInt)
        , testGroup
            "complete native admission is independent of source-head approximation"
            [ testCase (show relation ++ "/reverse=" ++ show reversed ++ "/valid=" ++ show valid) $ do
                let declarations = [("map", F.mapSort F.strSort F.boolSort), ("array", F.arraySort F.strSort (if valid then F.boolSort else F.intSort))]
                    environment = mempty{F.seSort = F.fromListSEnv declarations}
                    expression = atom reversed relation (F.EVar "map") (F.EVar "array")
                    parameter = C.ElabParam (Config.solverFlags Config.defConfig) "native Map/Array boundary" environment
                -- The environment-free source contract is deliberately unchanged.
                assertBool "standalone source admission changed" (either (const True) (const False) (C.sortExprE Nothing F.dummySpan (F.seSort environment) mempty expression))
                result <- evaluate (force (first show (C.elabExprE parameter Nothing expression)))
                assertBool (show result) (either (const (not valid)) (const valid) result)
            | relation <- [F.Ueq, F.Une]
            , reversed <- [False, True]
            , valid <- [False, True]
            ]
        , testGroup
            "configured source relation formation"
            [ testCase (show relation ++ "/reverse=" ++ show reversed ++ "/valid=" ++ show valid) $ do
                let declarations = F.fromListSEnv [("map", F.mapSort F.intSort F.boolSort), ("array", F.arraySort F.intSort (if valid then F.boolSort else F.intSort))]
                    environment = mempty{F.seSort = declarations}
                    expression = atom reversed relation (F.EVar "map") (F.EVar "array")
                    flags = Config.ElabFlags False False
                    expected = valid && relation `elem` [F.Ueq, F.Une]
                    checkAt = runReader (C.prepareSortCheck (Just environment) declarations) flags
                    sorted = C.sortExprE (Just environment) F.dummySpan declarations mempty expression
                    annotated = C.annotateExprEAt flags (Just environment) declarations "source relation formation" (Just F.boolSort) expression
                either (const False) (const True) sorted @?= expected
                either (const False) (const True) annotated @?= expected
                (C.checkSortAt checkAt F.dummySpan (Just F.boolSort) expression == Nothing) @?= expected
            | relation <- [F.Eq, F.Ne, F.Ueq, F.Une]
            , reversed <- [False, True]
            , valid <- [False, True]
            ]
        , testCase "configured carrier identity does not erase nominal Boolean aliases" $ do
            let declarations = F.fromListSEnv [("AliasA", F.boolSort), ("AliasB", F.boolSort), ("x", F.FObj "AliasA"), ("y", F.FObj "AliasB")]
                environment = mempty{F.seSort = declarations}
                expression = F.PAtom F.Eq (F.EVar "x") (F.EVar "y")
            assertBool "source equality admitted distinct nominal Boolean aliases" $
                either (const True) (const False) (C.sortExprE (Just environment) F.dummySpan declarations mempty expression)
        , testCase "source annotations do not perform native arithmetic encoding" $ do
            let expression = F.EBin F.Div (F.ECon (F.R 1)) (F.ECon (F.R 2))
                flags = Config.ElabFlags False False
                operation result = case result of
                    Right annotated -> case F.dropECst annotated of
                        F.EBin operator _ _ -> pure operator
                        other -> assertFailure (show other) >> pure F.Div
                    Left failure -> assertFailure (show failure) >> pure F.Div
            source <- operation (C.annotateExprEAt flags (Just mempty) mempty "source arithmetic" Nothing expression)
            native <- operation (C.elabExprEAt flags mempty mempty "native arithmetic" Nothing expression)
            source @?= F.Div
            native @?= F.RDiv
        , testGroup
            "string literal serialization options do not erase native string carriers"
            [ testCase (show strings) $ do
                let declarations = F.fromListSEnv [("string", F.strSort), ("integer", F.intSort)]
                    environment = F.symEnv Config.defConfig{Config.noStringTheory = not strings} declarations mempty [] mempty []
                    expression = F.PAtom F.Ueq (F.EVar "string") (F.EVar "integer")
                either (const False) (const True) (C.sortExprE (Just environment) F.dummySpan declarations mempty expression) @?= False
            | strings <- [False, True]
            ]
        , testGroup
            "source relation formation uses actual solver container lowering"
            [ testCase (name ++ "/" ++ show solver) $ do
                let declarations = F.fromListSEnv [("container", constructor F.strSort), ("array", F.arraySort F.strSort range)]
                    environment = F.symEnv Config.defConfig{Config.solver = solver} declarations mempty [] mempty []
                    expression = F.PAtom F.Ueq (F.EVar "container") (F.EVar "array")
                either (const False) (const True) (C.sortExprE (Just environment) F.dummySpan declarations mempty expression) @?= (solver == Config.Z3)
            | (name, constructor, range) <- [("Set", F.setSort, F.boolSort), ("Bag", F.bagSort, F.intSort)]
            , solver <- [Config.Z3, Config.Cvc5]
            ]
        , testCase "unused native context remains undemanded" $ do
            C.sortExprE (error "unused native context") F.dummySpan mempty mempty (F.ECon (F.I 0)) @?= Right F.intSort
        , quantifierBodyTests
        ]
  where
    scheme result = F.FAbs 42 (F.FFunc F.intSort result)
    call name = F.EApp (F.EVar name) (F.ECon (F.I 0))
    opaque = F.FApp (F.FTC (F.symbolFTycon (F.dummyLoc "Opaque")))
    position True phantom visible = F.arraySort phantom visible
    position False phantom visible = F.arraySort visible phantom
    ordered True = reverse
    ordered False = id
    atom :: Bool -> F.Brel -> F.Expr -> F.Expr -> F.Expr
    atom True relation left right = F.PAtom relation right left
    atom False relation left right = F.PAtom relation left right

accepted :: Config.ElabFlags -> [(F.Symbol, F.Sort)] -> F.Expr -> IO ()
accepted flags declarations expression = do
    let environment = mempty{F.seSort = F.fromListSEnv declarations}
    acceptedIn flags environment expression

acceptedIn :: Config.ElabFlags -> F.SymEnv -> F.Expr -> IO ()
acceptedIn flags environment expression = do
    let parameter = C.ElabParam flags "native carrier inference" environment
    result <- evaluate (force (first show (C.elabExprE parameter Nothing expression)))
    case result of
        Left failure -> assertFailure (show failure)
        Right _ -> pure ()

quantifierBodyTests :: TestTree
quantifierBodyTests =
    testGroup
        "quantifier body formation"
        [ testCase (api ++ "/" ++ name ++ "/" ++ position ++ "/" ++ bodyName) $ do
            result <- evaluate (force (first (map (show . F.errMsg) . F.errs) (check (place (bind body)))))
            assertBool (show result) $ case (result, expected) of
                (Left [actual], Left [message]) -> message `elem` map (dropWhile isSpace) (lines actual)
                _ -> result == expected
        | (name, bind) <- [("forall", F.PAll [("x", F.intSort)]), ("exists", F.PExist [("x", F.intSort)])]
        , (bodyName, body, expected) <-
            [ ("integer", F.ECon (F.I 1), Left ["Expressions 1 should have bool sort, but has int"])
            , ("Boolean", F.PTrue, Right F.boolSort)
            ]
        , (position, place) <- [("direct", id), ("inside equality", \expression -> F.PAtom F.Eq expression body)]
        , (api, check) <-
            [ ("source sort", C.sortExprE Nothing F.dummySpan mempty mempty)
            , ("source annotation", fmap (const F.boolSort) . C.annotateExprEAt flags (Just mempty) mempty "quantifier body" (Just F.boolSort))
            , ("configured elaboration", fmap (const F.boolSort) . C.elabExprEAt flags mempty mempty "quantifier body" (Just F.boolSort))
            ]
        ]
  where
    flags = Config.solverFlags Config.defConfig
