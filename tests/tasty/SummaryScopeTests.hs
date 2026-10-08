{-# LANGUAGE OverloadedStrings #-}

module SummaryScopeTests (tests) where

import Control.Monad (forM_)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import EliminatedSharingSupport
import qualified Language.Fixpoint.Solver.Solution as Solution
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Solutions as Sol
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "summary lexical scope"
        ( [ testCase label (check label expected True fixture)
          | (label, expected, fixture) <-
                [ ("generated definition avoids lexical binder", False, lexicalName True)
                , ("lexical binder retains false body", True, lexicalName False)
                , ("lexical native-name shadow remains local", False, lexicalNameAt "bool_to_int" True)
                , ("lexical native-name shadow retains false body", True, lexicalNameAt "bool_to_int" False)
                ]
          ]
            ++ [testCase "lexical names do not make nominal actual casts well-sorted" lexicalActualSorts]
            ++ [ testCase label (observed label expected (refreshedBinder zero ambient guarded))
               | zero <- [False, True]
               , ambient <- [False, True]
               , guarded <- [False, True]
               , let expected = if zero then guarded else not guarded
                     label = "refreshed binder (zero arity, ambient, guarded) " ++ show (zero, ambient, guarded)
               ]
            ++ [ testCase label (observed label (not guarded) (laterLocal guarded))
               | guarded <- [False, True]
               , let label = "later lexical actual remains local " ++ show guarded
               ]
            ++ [ testCase label $ do
                    observed label (not guarded) (specializedScope sort nested guarded True)
                    length (fst (sharedObservation (specializedScope sort nested guarded True)))
                        @?= length (fst (sharedObservation (specializedScope sort nested guarded False)))
               | sort <- [F.boolSort, F.FInt]
               , nested <- [False, True]
               , guarded <- [False, True]
               , let label = "cached specialization retains nested binder " ++ show (sort, nested, guarded)
               ]
            ++ [ testCase label (observed label (not guarded) (unusedQualifier guarded))
               | guarded <- [False, True]
               , let label = "unobserved qualifier is not demanded " ++ show guarded
               ]
        )

observed :: String -> Bool -> Fixture -> Assertion
observed label expected fixture = do
    assertBool "the observation emits a definition" (not (null (fst (sharedObservation fixture))))
    check label expected True fixture

sharedObservation :: Fixture -> ([F.Equation], F.Expr)
sharedObservation (info, solution, constraint) =
    Solution.lhsPredShared cfg (Solution.prepareSummaryState scope info) scope mempty info solution constraint
  where
    scope = S.insert "ghost" $ S.fromList [name | (_, (name, _, _)) <- F.bindEnvToList (F.bs info)]

lexicalName :: Bool -> Fixture
lexicalName = lexicalNameAt (F.tempSymbol "eliminated_summary" (0 :: Integer))

lexicalNameAt :: F.Symbol -> Bool -> Fixture
lexicalNameAt name guarded = (info, solution, constraint)
  where
    info = mempty{F.bs = bindings, F.ws = M.singleton (kvar 0) (F.WfC mempty ("v0", F.FInt, kvar 0) ())}
    body = use 0 name
    predicate = F.PAll [(name, F.FInt)] (if guarded then F.PImp (F.EEq (var name) (int 0)) body else body)
    bindings =
        F.bindEnvFromList
            [ binding 0 "y0" F.FInt (F.EEq (var "y0") (int 0))
            , binding 1 "v0" F.FInt F.PTrue
            , binding 2 "target" F.boolSort predicate
            ]
    cube = Sol.Cube (F.fromListIBindEnv [0]) (F.mkSubst [("v0", var "y0")]) 0 []
    solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) mempty)
    constraint = F.SimpC (F.fromListIBindEnv [2]) F.PFalse (Just 99) 2 [] ()

lexicalActualSorts :: Assertion
lexicalActualSorts =
    forM_ ["alpha", "other"] $ \name ->
        forM_ [F.boolSort, F.FObj "alpha"] $ \annotation -> do
            let occurrence = F.PKVar (kvar 0) mempty (F.mkKVarSubst [("formal", F.ECst F.PTrue annotation)])
                bindings =
                    F.bindEnvFromList
                        [ binding 0 "y" F.boolSort (F.EEq (var "y") F.PFalse)
                        , binding 1 "formal" F.boolSort F.PTrue
                        , binding 2 "target" F.boolSort (F.PAll [(name, F.boolSort)] occurrence)
                        ]
                cube = Sol.Cube (F.fromListIBindEnv [0]) (F.mkSubst [("formal", var "y")]) 0 []
                info = mempty{F.bs = bindings, F.ws = M.singleton (kvar 0) (F.WfC mempty ("formal", F.boolSort, kvar 0) ())}
                solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) mempty)
                constraint = F.SimpC (F.fromListIBindEnv [2]) F.PFalse (Just 99) 2 [] ()
                scope = S.fromList ["y", "formal", "target"]
                initial = Solution.prepareSummaryState scope info
                (definitions, predicate) = Solution.lhsPredShared cfg initial scope mempty info solution constraint
                define equation = F.ELet (F.eqName equation) (foldr F.ELam (F.eqBody equation) (F.eqArgs equation))
                shared = foldr define predicate definitions
                expanded = Solution.lhsPred cfg scope mempty info solution constraint
                expected = if annotation == F.boolSort then mempty else S.singleton "formal"
            -- A rejected implicit actual leaves its formal unsubstituted in
            -- both interpretations. Merely renaming a term binder cannot
            -- turn the unrelated nominal sort into Bool.
            mapM_ (\body -> F.syms body @?= expected) [expanded, shared]

-- If the surrounding declaration owns ##0, source interpretation refreshes
-- the quantifier to ##1. Reserving only the unexpanded source cannot protect
-- a summary subsequently allocated under that fresh binder. The zero-arity
-- cases distinguish both SAT and UNSAT, not just malformed applications.
refreshedBinder :: Bool -> Bool -> Bool -> Fixture
refreshedBinder zero ambient guarded = (info, solution, constraint)
  where
    name = F.tempSymbol "eliminated_summary" (0 :: Integer)
    scalar = if zero then F.boolSort else F.FInt
    occurrence = F.PKVar (kvar 0) mempty (if zero then mempty else F.mkKVarSubst [("v0", var name)])
    guard = if zero then var name else F.EEq (var name) (int 0)
    body = if guarded then F.PImp guard occurrence else occurrence
    leaf
        | not zero = F.EEq (var "y0") (int 0)
        | guarded = F.PFalse
        | otherwise = F.PTrue
    bindings =
        F.bindEnvFromList $
            [ binding 0 "y0" scalar leaf
            , binding 1 "v0" scalar F.PTrue
            , binding 2 "target" F.boolSort (F.PAll [(name, scalar)] body)
            ]
                ++ [binding 3 name scalar F.PTrue | ambient]
    info = mempty{F.bs = bindings, F.ws = M.singleton (kvar 0) (F.WfC mempty ("v0", scalar, kvar 0) ())}
    cube = Sol.Cube (F.fromListIBindEnv [0]) (if zero then mempty else F.mkSubst [("v0", var "y0")]) 0 []
    solution = Sol.Sol mempty (M.singleton (kvar 0) [cube]) (M.singleton (kvar 0) mempty)
    constraint = F.SimpC (F.fromListIBindEnv [2]) F.PFalse (Just 99) 2 [] ()

-- The first top-level occurrence allocates a summary before the later
-- quantifier is visited. Its Int actual is a local variable, not a reference
-- to the same-spelled generated Boolean function. Filtering that actual
-- would leave v0 = 0 and falsely contradict the explicit v0 /= 0 premise.
laterLocal :: Bool -> Fixture
laterLocal guarded = (info{F.bs = bindings}, solution, constraint)
  where
    (info, solution, _) = lexicalName True
    name = F.tempSymbol "eliminated_summary" (0 :: Integer)
    actual = F.EBin F.Plus (var name) (int 1)
    occurrence value = F.PKVar (kvar 0) mempty (F.mkKVarSubst [("v0", value)])
    body = if guarded then F.PImp (F.EEq actual (int 0)) (occurrence actual) else occurrence actual
    bindings =
        F.bindEnvFromList
            [ binding 0 "y0" F.FInt (F.EEq (var "y0") (int 0))
            , binding 1 "v0" F.FInt (F.PAtom F.Ne (var "v0") (int 0))
            , binding 2 "target" F.boolSort (F.PAnd [occurrence (int 0), F.PAll [(name, F.FInt)] body])
            ]
    constraint = F.SimpC (F.fromListIBindEnv [1, 2]) F.PFalse (Just 99) 2 [] ()

-- A genuine free dependency and an unrelated bound variable have the same
-- spelling in different scopes. Nonidentity type substitution must rename
-- only the dependency, including when reached through another definition.
-- Repetition observes the same specialization cache without adding equations.
specializedScope :: F.Sort -> Bool -> Bool -> Bool -> Fixture
specializedScope sort nested guarded repeated = (info, solution, constraint)
  where
    name = F.tempSymbol "eliminated_summary" (0 :: Integer)
    leaf = F.PKVar (kvar 0) mempty mempty
    middle = F.PKVar (kvar 1) mempty mempty
    local = if guarded then F.PImp (var name) (var name) else var name
    top = F.PKVar (kvar (if nested then 2 else 1)) (M.singleton "element" sort) mempty
    bindings =
        F.bindEnvFromList
            [ binding 0 "leaf" F.boolSort F.PTrue
            , binding 1 "elementValue" (F.FObj "element") (F.EEq (var "elementValue") (var "elementValue"))
            , binding 2 "middle" F.boolSort (F.PAnd [leaf, F.PAll [(name, F.boolSort)] local])
            , binding 3 "outer" F.boolSort middle
            , binding 4 "target" F.boolSort (if repeated then F.PAnd [top, top] else top)
            ]
    info = mempty{F.bs = bindings, F.ws = M.fromList [(kvar index, F.WfC mempty ("vv", F.boolSort, kvar index) ()) | index <- [0, 1, 2]]}
    cubes =
        [ (kvar 0, [Sol.Cube (F.fromListIBindEnv [0]) mempty 0 []])
        , (kvar 1, [Sol.Cube (F.fromListIBindEnv [1, 2]) mempty 1 []])
        , (kvar 2, [Sol.Cube (F.fromListIBindEnv [3]) mempty 2 []])
        ]
    solution = Sol.Sol mempty (M.fromList cubes) (M.fromList [(key, mempty) | (key, _) <- cubes])
    constraint = F.SimpC (F.fromListIBindEnv [4]) F.PFalse (Just 99) 4 [] ()

unusedQualifier :: Bool -> Fixture
unusedQualifier guarded =
    (info, solution{Sol.sMap = M.singleton (kvar 99) (Sol.qb [error "unobserved qualifier instantiation"])}, constraint)
  where
    (info, solution, constraint) = lexicalName guarded
