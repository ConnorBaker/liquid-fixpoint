{-# LANGUAGE OverloadedStrings #-}

module QueryAuthorityTests (tests) where

import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad (filterM)
import Control.Monad.State.Strict (evalStateT)
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set
import Data.List (isInfixOf)
import qualified Data.Store as Store
import qualified Language.Fixpoint.Graph.Deps as Deps
import qualified Language.Fixpoint.Graph.Partition as Partition
import Language.Fixpoint.Parse (rr')
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Solver.Monad as SM
import qualified Language.Fixpoint.Solver.Stats as Stats
import qualified Language.Fixpoint.SortCheck as C
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "saved equation authority"
        [ testGroup
            "text roundtrip"
            [ testCase label $ do
                let original = query policy
                    decoded = rr' "authority-roundtrip" (show (F.toFixpoint Config.defConfig original)) :: F.FInfo ()
                F.aenvNative (F.ae decoded) @?= policy
                F.aenvEqs (F.ae decoded) @?= F.aenvEqs (F.ae original)
            | (label, policy) <- policies
            ]
        , testGroup
            "binary roundtrip"
            [ testCase label $
                Store.decode (Store.encode (query policy)) @?= Right (query policy)
            | (label, policy) <- policies
            ]
        , testCase "legacy directive absence remains all-native" $
            F.aenvNative (F.ae (rr' "legacy" "" :: F.FInfo ())) @?= Nothing
        , testCase "repeated authority bounds intersect, never union" $
            F.aenvNative (F.ae (rr' "bounds" "nativeequations [f;g]\nnativeequations [g;h]\n" :: F.FInfo ()))
                @?= Just (Set.singleton "g")
        , testCase "query composition intersects bounds without dropping equations" $ do
            let left = query (Just (Set.fromList ["f", "g"]))
                right = query (Just (Set.fromList ["g", "h"]))
                combined = left <> right
            F.aenvNative (F.ae combined) @?= Just (Set.singleton "g")
            F.aenvEqs (F.ae combined) @?= F.aenvEqs (F.ae left) ++ F.aenvEqs (F.ae right)
        , testCase "all policy compositions obey the meet law" $
            map (\(left, right) -> F.aenvNative (environment left <> environment right)) pairs
                @?= map (uncurry meet) pairs
        , testCase "empty query is the authority identity" $
            [(mempty <> query policy, query policy <> mempty) | (_, policy) <- policies]
                @?= [(query policy, query policy) | (_, policy) <- policies]
        , testCase "authority composition is associative" $
            [(environment a <> environment b) <> environment c | (_, a) <- policies, (_, b) <- policies, (_, c) <- policies]
                @?= [environment a <> (environment b <> environment c) | (_, a) <- policies, (_, b) <- policies, (_, c) <- policies]
        , testGroup
            "query transformations retain their authority"
            [ testCase label $ do
                let original = (query policy){F.cm = Map.fromList (F.addIds [constraint])}
                    sliced = Deps.slice Config.defConfig original
                    partitions = Partition.partition' Nothing sliced
                F.aenvNative (F.ae sliced) @?= policy
                assertBool "the control has a real partition" (not (null partitions))
                map (F.aenvNative . F.ae) partitions @?= replicate (length partitions) policy
                (_, source, normalized, _) <- Solver.simplifyFInfo Config.defConfig original
                map (F.aenvNative . F.ae) [source, normalized] @?= [policy, policy]
            | (label, policy) <- policies
            ]
        , filterValidTests
        , emptySliceTests
        ]
  where
    pairs = [(a, b) | (_, a) <- policies, (_, b) <- policies]
    meet Nothing right = right
    meet left Nothing = left
    meet (Just left) (Just right) = Just (Set.intersection left right)
    constraint = F.mkSubC F.emptyIBindEnv (refinement F.PTrue) (refinement F.PFalse) Nothing [] ()
    refinement predicate = F.RR F.intSort (F.Reft ("v", predicate))

emptySliceTests :: TestTree
emptySliceTests =
    testGroup "empty target reachability" $
        [ testCase label $ do
            let original = catalog{F.cm = Map.singleton 1 constraint}
                expected :: F.FInfo ()
                expected = original{F.cm = mempty, F.ws = mempty}
            -- Binary equality observes every retained field, including native
            -- capability metadata that nominal Sort equality does not observe.
            Store.encode (Deps.slice Config.defConfig original) @?= Store.encode expected
        | (label, constraint) <-
            [ ("tautological RHS", row mempty F.PTrue)
            , ("dangling environment ID", row (F.fromListIBindEnv [999]) F.PTrue)
            , ("missing WF of an untargeted predicate", row mempty (F.PKVar (F.KV "undeclared") mempty mempty))
            ]
        ]
            ++ [ testCase "noslice retains the complete query" $ do
                    let original = (query Nothing){F.cm = Map.singleton 1 (row mempty F.PTrue)}
                    Store.encode (Deps.slice Config.defConfig{Config.noslice = True} original) @?= Store.encode original
               , testCase "a false target is not an empty-root query" $ do
                    let original = (query Nothing){F.cm = Map.singleton 1 (row mempty F.PFalse)}
                    Store.encode (Deps.slice Config.defConfig original) @?= Store.encode original
               , testCase "rootless slicing retains native declaration rejection" $ do
                    let tycon = F.symbolFTycon (F.dummyLoc "Bad")
                        irregular = F.DDecl tycon 1 [F.DCtor (F.dummyLoc "BadC") [F.DField (F.dummyLoc "badField") (F.FApp (F.FTC tycon) F.FInt)]]
                        original = (query Nothing){F.cm = Map.singleton 1 (row mempty F.PTrue), F.ddecls = [irregular]}
                    failure <- try (Solver.simplifyFInfo Config.defConfig (Deps.slice Config.defConfig original) >> pure ()) :: IO (Either SomeException ())
                    case failure of
                        Left diagnostic -> assertBool (show diagnostic) ("Non-regular datatype" `isInfixOf` show diagnostic)
                        Right () -> assertFailure "slicing hid an invalid native declaration"
               , testCase "public solving still rejects a partial source AST before slicing" $ do
                    let original =
                            (query Nothing)
                                { F.bs = F.bindEnvFromList [(0, ("partial", F.RR F.FInt (F.Reft ("v", error "partial slice control")), ()))]
                                , F.cm = Map.singleton 1 (row (F.fromListIBindEnv [0]) (F.PKVar (F.KV "undeclared") mempty mempty))
                                }
                    failure <- try (Solver.solve Config.defConfig{Config.save = False} original >>= evaluate) :: IO (Either SomeException (F.Result (Integer, ())))
                    case failure of
                        Left diagnostic -> assertBool (show diagnostic) ("partial slice control" `isInfixOf` show diagnostic)
                        Right _ -> assertFailure "the public solver accepted a partial source AST"
               ]
  where
    declared = F.KV "declared"
    carrier = F.dummyLoc "CatalogCarrier"
    numeric = F.FTC (F.symbolNumInfoFTyCon carrier True False)
    string = F.FTC (F.mappendFTC (F.symbolFTycon carrier) F.strFTyCon)
    catalog =
        (query (Just Set.empty))
            { F.bs = F.bindEnvFromList [(0, ("catalogValue", F.trueSortedReft numeric, ()))]
            , F.ws = Map.singleton declared (F.WfC (F.fromListIBindEnv [0]) [("formal", F.FInt)] (declared) ())
            , F.gLits = F.fromListSEnv [("numericCarrier", numeric)]
            , F.dLits = F.fromListSEnv [("stringCarrier", string)]
            , F.kuts = F.KS (Set.singleton declared)
            , F.quals = [F.Q "CatalogQualifier" [F.QP "v" F.PatNone F.FInt] F.PTrue (F.dummyPos "empty-slice")]
            , F.bindInfo = Map.singleton 0 ()
            , F.ddecls = [F.DDecl (F.symbolFTycon (F.dummyLoc "CatalogData")) 0 [F.DCtor (F.dummyLoc "CatalogConstructor") []]]
            , F.hoInfo = F.HOI True True
            }
    row environment predicate = F.mkSubC environment (refinement F.PTrue) (refinement predicate) (Just 1) [] ()
    refinement predicate = F.RR F.boolSort (F.Reft ("v", predicate))

filterValidTests :: TestTree
filterValidTests =
    testGroup
        "pointwise validity filtering"
        [ testGroup
            (show solver)
            [ testCase "pointwise proofs preserve 32 ordered duplicate payloads" $ do
                let candidates = [(F.PAtom F.Ge x (integer (-index)), index `mod` 5) | index <- [0 .. 31]]
                (actual, counters) <- withFilterSolver solver $ do
                    accepted <- SM.filterValid F.dummySpan [] lhs candidates
                    counters <- SM.stats
                    pure (accepted, counters)
                actual @?= map snd candidates
                Stats.numChck counters @?= 32
                Stats.numVald counters @?= length candidates
            , testCase "mixed results agree with pointwise checks and retain order and duplicates" $ do
                let candidates :: [(F.Expr, Int)]
                    candidates = [(F.PAtom F.Ge x (integer 0), 4), (F.PAtom F.Gt x (integer 0), 9), (b, 4), (F.PNot b, 7), (F.PAtom F.Eq x x, 2), (F.PAtom F.Le x (integer 0), 4), (F.PTrue, 2)]
                (vacuous, actual, reference, checks) <- withFilterSolver solver $ do
                    vacuous <- SM.filterValid F.dummySpan [] F.PFalse [(F.PFalse, 0 :: Int)]
                    before <- SM.stats
                    accepted <- SM.filterValid F.dummySpan [] lhs candidates
                    after <- SM.stats
                    reference <- SM.liftSMT $ SMT.smtBracket "pointwiseLHS" $ do
                        SMT.smtAssert lhs
                        retained <- filterM (\(predicate, _) -> SMT.smtBracket "pointwiseRHS" (SMT.smtAssert (F.PNot predicate) >> SMT.smtCheckUnsat)) candidates
                        pure (map snd retained)
                    pure (vacuous, accepted, reference, Stats.numChck after - Stats.numChck before)
                vacuous @?= [0]
                actual @?= [4, 4, 2, 2]
                actual @?= reference
                assertBool "mixed group exceeded the pointwise query bound" (0 < checks && checks <= length candidates)
            , testGroup
                "serialization cannot be skipped"
                [ testCase label $ do
                    outcome <- try (withFilterSolver solver (SM.filterValid F.dummySpan [] left candidates)) :: IO (Either F.Error [Int])
                    case outcome of
                        Left failure -> assertBool "unexpected failure instead of expression serialization" (any (isInfixOf "smtlib2 Pred" . show . F.errMsg) (F.errs failure))
                        Right _ -> assertFailure "validity filtering skipped an unserializable expression"
                | (label, left, candidates) <-
                    [ ("empty candidates still check their LHS", unresolved, [])
                    , ("false premises still serialize every candidate", F.PFalse, [(F.PFalse, 0), (unresolved, 1)])
                    ]
                ]
            ]
        | solver <- [Config.Z3, Config.Cvc5]
        ]
  where
    lhs, x, b, unresolved :: F.Expr
    lhs = F.PAnd [F.PAtom F.Ge x (integer 0), b]
    x = F.EVar "filter_x"
    b = F.EVar "filter_b"
    unresolved = F.PKVar (F.KV "unresolved") mempty mempty
    integer :: Int -> F.Expr
    integer = F.ECon . F.I . fromIntegral

withFilterSolver :: Config.SMTSolver -> SM.SolveM () a -> IO a
withFilterSolver solver action =
    bracket (SMT.makeContextNoLog cfg) SMT.cleanupContext $ \context ->
        evalStateT
            (SM.liftSMT (SMT.smtDecls declarations) >> action)
            (SM.SS context{SMT.ctxSymEnv = environment} mempty (C.ElabParam (Config.solverFlags cfg) "validity filtering" environment))
  where
    cfg = Config.defConfig{Config.solver = solver}
    declarations = [("filter_x", F.FInt), ("filter_b", F.boolSort)]
    environment = F.emptySymEnv{F.seSort = F.fromListSEnv declarations}

policies :: [(String, Maybe (Set.HashSet F.Symbol))]
policies =
    [ ("raw all-native", Nothing)
    , ("source-only", Just Set.empty)
    , ("one certified owner", Just (Set.singleton "f"))
    , ("several certified owners", Just (Set.fromList ["f", "g"]))
    ]

environment :: Maybe (Set.HashSet F.Symbol) -> F.AxiomEnv
environment policy = mempty{F.aenvNative = policy}

query :: Maybe (Set.HashSet F.Symbol) -> F.FInfo ()
query policy =
    mempty
        { F.ae = (environment policy){F.aenvEqs = [F.mkEquation "f" [("x", F.intSort)] (F.EVar "x") F.intSort]}
        }
