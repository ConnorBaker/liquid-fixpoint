{-# LANGUAGE OverloadedStrings #-}

module ScopedSubstitutionTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Hashable (hash, hashWithSalt)
import Data.List (isInfixOf, sortOn, subsequences)
import qualified Language.Fixpoint.Horn.Info as Horn
import qualified Language.Fixpoint.Horn.Types as H
import qualified Language.Fixpoint.Misc as Misc
import Language.Fixpoint.Parse (rr')
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Sanitize as Sanitize
import qualified Language.Fixpoint.SortCheck as Check
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import qualified Language.Fixpoint.Types.Visitor as V
import SortInventoryTests (allocationBytes)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests = testGroup "Scoped substitutions" [coTests, sortTests, scrapeTests, conditionalScrapeTests, qualifierTests, typeApplicationTests]

qualifierTests :: TestTree
qualifierTests =
    testGroup
        "concrete qualifier vocabulary"
        [ testGroup "automatic candidates" $
            [ testCase label $ do
                let info = scrapeQuery [("a", F.FInt, predicate)] [([0], "v")]
                    candidates = Horn.scrapeFInfo Config.defConfig Config.Both info
                    horn = H.All (H.Bind "a" F.FInt (H.Reft predicate) ()) (H.Head (H.Reft F.PTrue) ())
                length candidates @?= count
                length (H.quals horn) @?= sourceCount
                assertBool "unknown predicate escaped into a candidate" (all (V.isConc . F.qBody) candidates)
            | (label, predicate, count, sourceCount) <-
                [ ("negative unknown", F.PNot unknown, 0, 0)
                , ("quantified unknown", F.PAll [("bound", F.FInt)] unknown, 0, 0)
                , ("let-bound unknown", F.ELet "bound" (F.EVar "a") unknown, 0, 0)
                , ("independent concrete conjunct", F.PAnd [comparison, F.PNot unknown], 1, 1)
                , ("concrete negation", F.PNot comparison, 1, 1)
                , ("concrete quantification", F.PAll [("bound", F.FInt)] comparison, 1, 1)
                , ("concrete let", F.ELet "bound" (F.EVar "a") comparison, 1, 1)
                , ("concrete conditional", F.EIte comparison F.PTrue F.PFalse, 2, 1)
                ]
            ]
        , testGroup "declarations are diagnosed, not discarded" $
            [ testCase label $ do
                let qualifiers = F.quals info
                case Sanitize.sanitize Config.defConfig (F.convertFormat info) of
                    Left failure ->
                        assertBool "missing source-located qualifier diagnostic" $
                            any
                                (\err -> F.errLoc err `elem` map F.srcSpan qualifiers && "Qualifier contains unknown predicates" `isInfixOf` show (F.errMsg err))
                                (F.errs failure)
                    Right _ -> assertFailure "non-concrete qualifier declaration was accepted"
            | (label, info) <-
                [ ("direct root", declaration unknown)
                , ("direct nested", declaration (F.PNot unknown))
                , ("parsed nested", rr' "nested-qualifier.fq" "qualif Recursive(a:int) { ~ $unknown[a := a] }")
                ]
            ]
        ]
  where
    unknown = F.PKVar (F.KV "unknown") mempty (F.mkKVarSubst [("a", F.EVar "a")])
    comparison = F.PAtom F.Ge (F.EVar "a") (F.ECon (F.I 0))
    declaration body = (mempty :: F.FInfo ()){F.quals = [F.mkQ "Recursive" [("a", F.FInt)] body (F.dummyPos "declared-qualifier")]}

typeApplicationTests :: TestTree
typeApplicationTests =
    testGroup
        "type application sort fields"
        [ testCase name $ do
            let input = F.ETApp (F.ECst (F.EVar "f") (F.FObj "a")) (F.FAbs 0 (F.FFunc (F.FObj "a") (F.FVar 0)))
                expected = F.ETApp (F.ECst (F.EVar "f") (F.FVar 0)) (F.FAbs 1 (F.FFunc (F.FVar 0) (F.FVar 1)))
            action (M.singleton "a" (F.FVar 0)) input @?= expected
        | (name, action) <- [("coercion substitution", V.applyCoSub), ("expression sort substitution", F.sortSubstInExpr)]
        ]

scrapeTests :: TestTree
scrapeTests =
    testGroup
        "scraping repeated environment facts"
        ( [ testCase label $ do
                let actual = scrape info
                    separate = concat [scrape info{F.cm = M.singleton key sub} | (key, sub) <- M.toList (F.cm info)]
                actual @?= Misc.sortNub separate
                length actual @?= count
                S.fromList (concatMap (map F.qpSort . F.qParams) actual) @?= S.fromList sorts
          | (label, info, count, sorts) <-
                [ ("identical inputs merge", duplicate, 1, [F.FInt])
                , ("same predicate retains different local sorts", mixed, 2, [F.FInt, F.FReal])
                , ("lhs shadow retains cyclic parameter order", ordered, 6, [F.FInt])
                , ("free names remain excluded", free, 0, [])
                , ("query globals remain available", free{F.gLits = F.fromListSEnv [("external", F.FInt)]}, 1, [F.FInt])
                , ("zero local parameters produce no qualifier despite declared globals", globalOnly, 0, [])
                , ("four local parameters produce no qualifier", fourParameters, 0, [])
                , ("same scope and lhs name retain different lhs sorts", shadowedSorts, 2, [F.FInt, F.FReal])
                , ("shared environment context retains every lhs and rhs predicate", ownPredicates, 3, [F.FInt])
                ]
          ]
            ++ [ testCase "scope projection agrees with complete Horn telescopes" $
                    forM_ [Config.No, Config.Head, Config.Both] $ \mode ->
                        forM_ (subsequences [0 .. 4]) $ \ids ->
                            forM_ ["a", "b", "v"] $ \value -> do
                                forM_ [[0 .. 4], [1024, -8, 97, 65, 33]] $ \identifiers -> do
                                    let source = scrapeQuery matrix [(ids, value)]
                                        rows = zip [0 ..] identifiers
                                        scope = F.fromListIBindEnv (99 : [new | (old, new) <- rows, old `elem` ids])
                                        lhs = F.RR F.FInt (F.Reft (value, F.PAtom F.Ge (F.EVar value) (F.ECon (F.I 0))))
                                        rhs = F.RR F.FInt (F.Reft ("right", F.PAtom F.Eq (F.EVar "right") (F.EVar "b")))
                                        info = source{F.bs = F.bindEnvFromList [(new, F.lookupBindEnv old (F.bs source)) | (old, new) <- rows], F.cm = M.singleton 0 (F.mkSubC scope lhs rhs Nothing [] ()), F.gLits = F.fromListSEnv [("external", F.FInt)]}
                                    Horn.scrapeFInfo Config.defConfig mode info @?= scrapeReference mode info
               , testCase "shared contexts agree with full telescopes across lhs shadowing" $
                    forM_ [Config.No, Config.Head, Config.Both] $ \mode ->
                        forM_ [shadowedSorts, ownPredicates, ordered] $ \info ->
                            Horn.scrapeFInfo Config.defConfig mode info @?= scrapeReference mode info
               , testCase "scope hashing and scraping ignore insertion order" $ do
                    let ids = [0 .. 4] ++ [i | i <- [5 .. 1023], hash i `mod` 32 == hash (0 :: Int) `mod` 32]
                        original = F.fromListIBindEnv ids
                        orders = [reverse ids, drop 3 ids ++ take 3 ids, ids ++ ids]
                    forM_ orders $ \order -> do
                        let reordered = F.fromListIBindEnv order
                            source = scrapeQuery matrix [(ids, "a"), (order, "b")]
                        reordered @?= original
                        forM_ [-1024, 0, 1, 97] $ \salt ->
                            hashWithSalt salt reordered @?= hashWithSalt salt original
                        M.size (M.fromList [(original, ()), (reordered, ())]) @?= 1
                        forM_ [Config.No, Config.Head, Config.Both] $ \mode ->
                            Horn.scrapeFInfo Config.defConfig mode source @?= scrapeReference mode source
               , testCase "repeated scopes do not rebuild all declarations" $ do
                    let bindings = [(name, F.FInt, F.PAtom F.Ge (F.EVar name) (F.ECon (F.I 0))) | i <- [0 .. 1023 :: Int], let name = F.symbol ("x" ++ show i)]
                        info = scrapeQuery bindings (replicate 128 ([0 .. 1023], "v"))
                        candidates = scrape info
                    _ <- evaluate (force info)
                    bytes <- allocationBytes candidates
                    length candidates @?= 1
                    assertBool ("scraping allocated " ++ show bytes ++ " bytes") (bytes <= 16 * 1024 * 1024)
               ]
        )
  where
    scrape = Horn.scrapeFInfo Config.defConfig Config.Both
    nonnegative = F.PAtom F.Ge (F.EVar "a") (F.ECon (F.I 0))
    duplicate = scrapeQuery [("a", F.FInt, nonnegative)] (replicate 4 ([0], "v"))
    mixed = scrapeQuery [("a", s, nonnegative) | s <- [F.FInt, F.FReal]] [([0], "v"), ([1], "v")]
    ordered = scrapeQuery [("a", F.FInt, F.PAtom F.Eq (F.EVar "a") (F.EBin F.Plus (F.EVar "b") (F.EVar "c"))), ("b", F.FInt, F.PTrue), ("c", F.FInt, F.PTrue)] [([0, 1, 2], "a"), ([0, 1, 2], "b")]
    free = scrapeQuery [("a", F.FInt, F.PAtom F.Eq (F.EVar "a") (F.EVar "external"))] (replicate 2 ([0], "v"))
    globalOnly = (scrapeQuery [("a", F.FInt, F.PAtom F.Ge (F.EVar "external") (F.ECon (F.I 0)))] [([0], "v")]){F.gLits = F.fromListSEnv [("external", F.FInt)]}
    fourParameters =
        scrapeQuery
            [ ("a", F.FInt, F.PAtom F.Eq (F.EBin F.Plus (F.EVar "a") (F.EVar "b")) (F.EBin F.Plus (F.EVar "c") (F.EVar "d")))
            , ("b", F.FInt, F.PTrue)
            , ("c", F.FInt, F.PTrue)
            , ("d", F.FInt, F.PTrue)
            ]
            [([0 .. 3], "v")]
    shadowedSorts =
        (scrapeQuery [("a", F.FInt, nonnegative)] [([0], "a"), ([0], "a")])
            { F.cm = M.fromList [(i, F.mkSubC (F.fromListIBindEnv [0]) (reft sort F.PTrue) (reft sort F.PTrue) Nothing [] ()) | (i, sort) <- zip [0 ..] [F.FInt, F.FReal]]
            }
      where
        reft sort predicate = F.RR sort (F.Reft ("a", predicate))
    ownPredicates =
        (scrapeQuery [("a", F.FInt, nonnegative)] [([0], "v"), ([0], "v")])
            { F.cm =
                M.fromList
                    [ (0, constraint (F.PAtom F.Ge (F.EVar "v") (F.ECon (F.I 10))) F.PTrue)
                    , (1, constraint F.PTrue (F.PAtom F.Le (F.EVar "v") (F.ECon (F.I (-1)))))
                    ]
            }
      where
        constraint left right = F.mkSubC (F.fromListIBindEnv [0]) (reft left) (reft right) Nothing [] ()
        reft predicate = F.RR F.FInt (F.Reft ("v", predicate))
    matrix =
        [ ("a", F.FInt, F.PAtom F.Eq (F.EVar "a") (F.EBin F.Plus (F.EVar "b") (F.EVar "c")))
        , ("b", F.FInt, F.PAll [("a", F.FInt)] (F.PAtom F.Ge (F.EVar "b") (F.EVar "a")))
        , ("c", F.FObj "alpha", F.PAtom F.Eq (F.EVar "c") (F.EVar "external"))
        , ("a", F.FReal, F.PNot (F.PKVar (F.KV "unknown") mempty mempty))
        , ("b", F.FObj "beta", nonnegative)
        ]

conditionalScrapeTests :: TestTree
conditionalScrapeTests =
    testGroup
        "conditional qualifier conjunctions"
        $ [ testCase label $ do
                let source = query predicate
                    expected = Horn.scrapeFInfo Config.defConfig Config.Both (query (F.PAnd conjuncts))
                    actual = Horn.scrapeFInfo Config.defConfig Config.Both source
                actual @?= expected
                actual @?= scrapeReference Config.Both source
                length actual @?= count
                assertBool "an original template was lost" (originalBodies predicate `S.isSubsetOf` S.fromList (map F.qBody actual))
          | (label, predicate, conjuncts, count) <-
                [ ("four-parameter conditional exposes two small candidates", conjunction p r, [p, r], 4)
                , ("usable original template survives", conjunction p q, [conjunction p q, p, q], 7)
                , ("nested consequent", conjunction p (conjunction q r), [p, q, r], 6)
                , ("nested condition", conjunction (conjunction p q) r, [p, q, r], 6)
                , ("nested conjunction", F.PAnd [p, conjunction q r], [p, conjunction q r, q, r], 9)
                , ("implication is not a conjunction", implication, [implication], 3)
                , ("negation is not a conjunction", negation, [negation], 3)
                , ("true alternative is not a conjunction", trueAlternative, [trueAlternative], 3)
                , ("false consequent is not a conjunction", falseConsequent, [falseConsequent], 3)
                ]
          ]
            ++ [ testCase "the original template retains a non-value argument fact" $ do
                    let positive = F.PAtom F.Gt (F.EVar "v") zero
                        other = F.PAtom F.Eq (F.EVar "x") zero
                        source = anchoredQuery (conjunction positive other)
                        mine = Horn.scrapeFInfo Config.defConfig Config.Both
                    forM_ [(True, mine source), (False, mine (anchoredQuery (F.PAnd [positive, other])))] $ \(expectedSafe, vocabulary) -> do
                        result <- Solver.solve Config.defConfig{Config.eliminate = Config.None, Config.cores = Just 1} source{F.quals = vocabulary}
                        case (expectedSafe, F.resStatus result) of
                            (True, F.Safe _) -> pure ()
                            (False, F.Unsafe _ failures) -> map fst failures @?= [2]
                            (_, status) -> assertFailure ("qualifier anchoring changed: " ++ show status)
               ]
  where
    p = F.PAtom F.Lt (F.EVar "a") (F.EVar "b")
    q = F.PAtom F.Eq (F.EVar "b") (F.EVar "c")
    r = F.PAtom F.Le (F.EVar "c") (F.EVar "d")
    conjunction left right = F.EIte left right F.PFalse
    implication = F.PImp p (conjunction p q)
    negation = F.PNot (conjunction p q)
    trueAlternative = F.EIte p q F.PTrue
    falseConsequent = F.EIte p F.PFalse q
    query predicate = scrapeQuery [(name, F.FInt, if name == "a" then predicate else F.PTrue) | name <- ["a", "b", "c", "d"]] [([0 .. 3], "v")]
    originalBodies predicate =
        S.fromList
            [ F.subst (F.mkSubst (zip (drop i names ++ take i names) (map (F.EVar . F.bindSymbol) [0 ..]))) part
            | part <- F.concConjuncts predicate
            , let names = reverse (sortOn id (S.toList (F.syms part)))
            , length names <= 3
            , i <- [0 .. length names - 1]
            ]
    zero = F.ECon (F.I 0)
    anchoredQuery premise =
        (mempty :: F.FInfo ())
            { F.bs = F.bindEnvFromList [(0, ("x", F.trueSortedReft F.FInt, ()))]
            , F.ws = M.singleton kvar (F.WfC scope ("v", F.FInt, kvar) ())
            , F.cm = M.fromList [(1, constraint 1 premise occurrence), (2, constraint 2 occurrence (F.PAtom F.Eq (F.EVar "x") zero))]
            }
      where
        kvar = F.KV "anchored"
        scope = F.fromListIBindEnv [0]
        occurrence = F.PKVar kvar mempty mempty
        constraint identifier left right = F.mkSubC scope (reft left) (reft right) (Just identifier) [] ()
        reft predicate = F.RR F.FInt (F.Reft ("v", predicate))

-- Interpret each FInfo scope as a complete Horn telescope, then ask the
-- existing Horn scraper for its candidates. All facts stay under the complete
-- telescope: BindEnv enumeration is not a dependent declaration order.
scrapeReference :: Config.Scrape -> F.FInfo () -> [F.Qualifier]
scrapeReference Config.No _ = []
scrapeReference mode info = Misc.sortNub $ filter closed $ concatMap scrape (M.elems (F.cm info))
  where
    closed = all (`F.memberSEnv` Check.globalEnv Config.defConfig info) . F.syms
    scrape sub = F.quals (Horn.hornFInfo Config.defConfig{Config.scrape = Config.Head} query)
      where
        lhs@(F.RR _ (F.Reft (value, _))) = F.slhs sub
        local = sortOn fst (F.envCs (F.bs info) (F.senv sub)) ++ [(value, lhs)]
        bodies = predicateAt value (F.srhs sub) : [predicateAt x reft | mode == Config.Both, (x, reft) <- local]
        cstr = foldr (\(x, F.RR t _) -> H.All (H.Bind x t (H.Reft F.PTrue) ())) (H.CAnd [H.Head (H.Reft p) () | p <- bodies]) local
        query = H.Query [] [] cstr mempty mempty [] [] [] [] [] [] [] []
    predicateAt name (F.RR _ (F.Reft (value, predicate))) = F.subst1 predicate (value, F.EVar name)

scrapeQuery :: [(F.Symbol, F.Sort, F.Expr)] -> [([F.BindId], F.Symbol)] -> F.FInfo ()
scrapeQuery bindings scopes =
    mempty
        { F.bs = F.bindEnvFromList [(i, (name, F.RR sort (F.Reft (name, predicate)), ())) | (i, (name, sort, predicate)) <- zip [0 ..] bindings]
        , F.cm = M.fromList [(i, F.mkSubC (F.insertsIBindEnv ids F.emptyIBindEnv) reft reft Nothing [] ()) | (i, (ids, value)) <- zip [0 ..] scopes, let reft = F.RR F.FInt (F.Reft (value, F.PTrue))]
        }

coTests :: TestTree
coTests =
    testGroup
        "simultaneous sort action under quantifiers"
        [ testGroup
            "each owned field once"
            [ testCase name $ do
                let input = outer [("x", coA)] (inner [("y", coA)] coEquality)
                    expected = outer [("x", coB)] (inner [("y", coB)] coEquality)
                    actual = V.applyCoSub coChain input
                actual @?= expected
                show actual @?= show expected
                Check.checkSortExpr Nothing F.dummySpan mempty input @?= Just F.boolSort
                Check.checkSortExpr Nothing F.dummySpan mempty actual @?= Just F.boolSort
            | (name, outer, inner) <-
                [ ("forall/exists", F.PAll, F.PExist)
                , ("exists/forall", F.PExist, F.PAll)
                , ("forall/forall", F.PAll, F.PAll)
                , ("exists/exists", F.PExist, F.PExist)
                ]
            ]
        , testCase "immediate cast remains simultaneous" $ do
            let input = F.PAll [("x", coA)] (F.ECst (F.EVar "x") coA)
                expected = F.PAll [("x", coB)] (F.ECst (F.EVar "x") coB)
            V.applyCoSub coChain input @?= expected
        , testCase "a swap does not compose with itself in a child" $ do
            let input = F.PAll [("x", coA)] (F.PExist [("y", coA)] coEquality)
                expected = F.PAll [("x", coB)] (F.PExist [("y", coB)] coEquality)
                swap = M.fromList [("a", coB), ("b", coA)]
            V.applyCoSub swap input @?= expected
            V.applyCoSub swap expected @?= input
        , testCase "empty action is identity" $
            V.applyCoSub mempty (F.PAll [("x", coA)] (F.PExist [("y", coA)] coEquality))
                @?= F.PAll [("x", coA)] (F.PExist [("y", coA)] coEquality)
        , testCase "unrelated incompatible coordinate remains incompatible" $ do
            let input = F.PAll [("x", coA)] (F.PExist [("y", F.FObj "other")] coEquality)
            Check.checkSortExpr Nothing F.dummySpan mempty input @?= Nothing
            Check.checkSortExpr Nothing F.dummySpan mempty (V.applyCoSub coChain input) @?= Nothing
        , testCase "unbound operand is not admitted" $ do
            let input = F.PAll [("x", coA)] coEquality
            Check.checkSortExpr Nothing F.dummySpan mempty (V.applyCoSub coChain input) @?= Nothing
        ]

coA, coB :: F.Sort
coA = F.FObj "a"
coB = F.FObj "b"

coChain :: V.CoSub
coChain = M.fromList [("a", coB), ("b", F.intSort)]

coEquality :: F.Expr
coEquality = F.PAtom F.Eq (F.EVar "x") (F.EVar "y")

sortTests :: TestTree
sortTests =
    testGroup
        "capture-avoiding symbolic sort substitution"
        ( [ testCase label $ do
                let actual = F.sortSubst substitution input
                assertBool
                    (show actual ++ " differs from " ++ show expected)
                    (sortAlpha [] [] actual expected)
                sortFree actual @?= sortFree expected
          | (label, substitution, input, expected) <- sortCases
          ]
            ++ [testCase "successive actions compose up to alpha-equivalence" sortComposition]
        )

sortComposition :: IO ()
sortComposition =
    forM_ [input | (_, _, input, _) <- sortCases] $ \input ->
        forM_ substitutions $ \first ->
            forM_ substitutions $ \second -> do
                let combined = M.map (F.sortSubst second) first `M.union` second
                    sequential = F.sortSubst second (F.sortSubst first input)
                    simultaneous = F.sortSubst combined input
                assertBool
                    (show (input, first, second, sequential, simultaneous))
                    (sortAlpha [] [] sequential simultaneous)
  where
    substitutions =
        [ mempty
        , M.singleton "a" (F.FVar 0)
        , M.singleton "b" (F.FVar 1)
        , M.fromList [("a", sortB), ("b", sortA)]
        , M.fromList [("a", sortB), ("b", F.intSort)]
        , M.singleton "a" (F.FAbs 0 (F.FFunc sortB (F.FVar 0)))
        ]

sortCases :: [(String, F.SortSubst, F.Sort, F.Sort)]
sortCases =
    [
        ( "free range index is not captured"
        , one (F.FVar 0)
        , F.FAbs 0 (F.FFunc sortA (F.FVar 0))
        , F.FAbs 1 (F.FFunc (F.FVar 0) (F.FVar 1))
        )
    ,
        ( "vacuous binder cannot capture image"
        , one (F.FVar 0)
        , F.FAbs 0 sortA
        , F.FAbs 1 (F.FVar 0)
        )
    ,
        ( "nested same-index binders have lexical ownership"
        , one (F.FVar 0)
        , F.FAbs 0 (F.FFunc (F.FVar 0) (F.FAbs 0 (F.FFunc sortA (F.FVar 0))))
        , F.FAbs 1 (F.FFunc (F.FVar 1) (F.FAbs 2 (F.FFunc (F.FVar 0) (F.FVar 2))))
        )
    ,
        ( "fresh coordinate avoids free target index"
        , one (F.FVar 0)
        , F.FAbs 0 (F.FFunc (F.FVar 1) (F.FFunc sortA (F.FVar 0)))
        , F.FAbs 2 (F.FFunc (F.FVar 1) (F.FFunc (F.FVar 0) (F.FVar 2)))
        )
    ,
        ( "image binders keep their own ownership"
        , one (F.FAbs 0 (F.FVar 0))
        , F.FAbs 0 (F.FFunc sortA (F.FVar 0))
        , F.FAbs 0 (F.FFunc (F.FAbs 0 (F.FVar 0)) (F.FVar 0))
        )
    ,
        ( "negative free indices are retained"
        , one (F.FVar (-1))
        , F.FAbs (-1) (F.FFunc sortA (F.FVar (-1)))
        , F.FAbs 0 (F.FFunc (F.FVar (-1)) (F.FVar 0))
        )
    ,
        ( "large binder label does not overflow freshness"
        , one (F.FVar maxBound)
        , F.FAbs maxBound (F.FFunc sortA (F.FVar maxBound))
        , F.FAbs 0 (F.FFunc (F.FVar maxBound) (F.FVar 0))
        )
    ,
        ( "replacement is simultaneous"
        , M.fromList [("a", sortB), ("b", F.intSort)]
        , F.FAbs 0 (F.FFunc sortA sortB)
        , F.FAbs 0 (F.FFunc sortB F.intSort)
        )
    ,
        ( "empty substitution is identity"
        , mempty
        , F.FAbs 0 (F.FFunc sortA (F.FVar 0))
        , F.FAbs 0 (F.FFunc sortA (F.FVar 0))
        )
    ,
        ( "bound indices are not substitution coordinates"
        , one F.intSort
        , F.FAbs 0 (F.FVar 0)
        , F.FAbs 0 (F.FVar 0)
        )
    ,
        ( "nominal application fields are transported"
        , one (F.FVar 0)
        , F.FAbs 0 (F.FApp (F.FVar 0) sortA)
        , F.FAbs 1 (F.FApp (F.FVar 1) (F.FVar 0))
        )
    ]
  where
    one s = M.singleton "a" s

sortA, sortB :: F.Sort
sortA = F.FObj "a"
sortB = F.FObj "b"

sortFree :: F.Sort -> S.HashSet Int
sortFree (F.FVar i) = S.singleton i
sortFree (F.FAbs i body) = S.delete i (sortFree body)
sortFree (F.FFunc x y) = sortFree x <> sortFree y
sortFree (F.FApp x y) = sortFree x <> sortFree y
sortFree _ = mempty

sortAlpha :: [Int] -> [Int] -> F.Sort -> F.Sort -> Bool
sortAlpha left right (F.FVar i) (F.FVar j) =
    case (sortPosition i left, sortPosition j right) of
        (Nothing, Nothing) -> i == j
        (Just p, Just q) -> p == q
        _ -> False
sortAlpha left right (F.FAbs i x) (F.FAbs j y) = sortAlpha (i : left) (j : right) x y
sortAlpha left right (F.FFunc x y) (F.FFunc u v) = sortAlpha left right x u && sortAlpha left right y v
sortAlpha left right (F.FApp x y) (F.FApp u v) = sortAlpha left right x u && sortAlpha left right y v
sortAlpha _ _ x y = x == y

sortPosition :: Int -> [Int] -> Maybe Int
sortPosition _ [] = Nothing
sortPosition x (y : ys)
    | x == y = Just 0
    | otherwise = (+ 1) <$> sortPosition x ys
