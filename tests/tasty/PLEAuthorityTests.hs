{-# LANGUAGE OverloadedStrings #-}

module PLEAuthorityTests (tests) where

import qualified Data.ByteString as B
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (sort)
import qualified Data.Store as Store
import Language.Fixpoint.Parse (rr')
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.SortCheck as SC
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import qualified Language.Fixpoint.Utils.Files as Files
import System.Exit (ExitCode (..))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "PLE demand and equation authority"
        [ equationInstantiationTests
        , testCase "formed call unfolds under its conditional branch" $
            check [] sourceOnly guardedGood
        , testCase "branch facts do not reach another constraint" $
            check [2] sourceOnly guardedPair
        , testCase "branch cache does not reach a sibling expression" $
            check [1] sourceOnly guardedSibling
        , testCase "guarded assumption does not publish an unconditional equation" $
            check [1] sourceOnly guardedAssumption
        , testCase "inferred qualifier is not a new source demand" $
            check [3] sourceOnly inferredDemand
        , testCase "raw total equations retain extensional unfolding" $
            check [] Nothing (callbackQuery False)
        , testCase "certified total equations retain extensional unfolding" $
            check [] (Just (S.fromList ["f", "g", "first"])) (callbackQuery False)
        , testCase "extensionality does not invent a source demand" $
            check [1] sourceOnly (callbackQuery False)
        , testCase "certified wrapper does not authorize its restricted callback" $
            check [1] (Just (S.singleton "first")) (callbackQuery True)
        , testGroup
            "measure instances survive constructor substitution"
            [ testCase (show (solver, direct, valid)) $
                withSystemTempDirectory "ple-measure-instance" $ \path -> do
                    result <- Solver.solve (config path){C.solver = solver} (measureQuery direct valid)
                    assertResult (if valid then [] else [1]) result
            | solver <- [C.Z3, C.Cvc5]
            , direct <- [False, True]
            , valid <- [False, True]
            ]
        , testGroup
            "local constant assumptions do not capture binders"
            [ testCase (show (solver, letBound, valid)) $
                withSystemTempDirectory "ple-local-shadow" $ \path -> do
                    result <- Solver.solve (config path){C.solver = solver, C.noEnvReduction = True} (localShadowQuery letBound valid)
                    assertResult (if valid then [] else [1]) result
            | solver <- [C.Z3, C.Cvc5]
            , letBound <- [False, True]
            , valid <- [False, True]
            ]
        , testGroup
            "ANF-named let binders remain lexical"
            [ testCase (show (solver, valid)) $
                withSystemTempDirectory "ple-anf-shadow" $ \path -> do
                    result <- Solver.solve (config path){C.solver = solver, C.noEnvReduction = True} (localShadowQueryAt "lq_anf$x" False True valid)
                    assertResult (if valid then [] else [1]) result
            | solver <- [C.Z3, C.Cvc5]
            , valid <- [False, True]
            ]
        , testGroup
            "rewrite schemas require a typed instance"
            [ testCase (name ++ " / " ++ show solver) $
                withSystemTempDirectory "ple-rewrite-instance" $ \path -> do
                    result <- Solver.solve (config path){C.solver = solver} query
                    assertResult [1] result
            | solver <- [C.Z3, C.Cvc5]
            , (name, query) <- incompatibleMeasures
            ]
        , testGroup
            "lexical binders do not authorize nominal rewrite instances"
            [ testCase (show valid) $
                withSystemTempDirectory "ple-nominal-scope" $ \path -> do
                    result <- Solver.solve (config path){C.extensionality = False} (nominalScopeQuery valid)
                    assertResult (if valid then [] else [1]) result
            | valid <- [False, True]
            ]
        , testCase "proactive equations normalize nested constructor eliminations" $
            check [] Nothing proactiveNestedMeasure
        , testCase "constructor-producing equations do not seed speculative growth" $
            check [] Nothing proactiveGrowthMeasure
        , testCase "a speculative equation does not demand a restricted helper" $
            check [1] sourceOnly proactiveRestrictedHelper
        , testGroup
            "saved text and binary query replay"
            [ testCase "raw total equations" $
                replay [] Nothing (callbackQuery False)
            , testCase "certified total equations" $
                replay [] (Just (S.fromList ["f", "g", "first"])) (callbackQuery False)
            , testCase "source-only partial equations stay restricted" $
                replay [1] sourceOnly (callbackQuery True)
            , testCase "certified wrapper cannot promote its callback" $
                replay [1] (Just (S.singleton "first")) (callbackQuery True)
            ]
        ]

equationInstantiationTests :: TestTree
equationInstantiationTests =
    testGroup
        "shared equation instantiation"
        [ testCase "named and negative-index formal ownership agree" $
            mapM_
                (\coordinate -> fmap SC.exprSortMaybe (instanceAt identityScheme coordinate F.FInt identityBody) @?= Right (Just F.FInt))
                [F.FObj "alpha", F.FVar (-1)]
        , testCase "same-spelled caller coordinate stays rigid" $
            fmap SC.exprSortMaybe (instanceAt identityScheme (F.FObj "alpha") (F.FObj "alpha") identityBody)
                @?= Right (Just (F.FObj "alpha"))
        , testCase "body-only named annotations do not become formal binders" $ do
            let body coordinate = F.ECoerc (F.FObj "outside") coordinate (F.EVar "x")
            case instanceAt identityScheme (F.FObj "alpha") F.FInt body of
                Right (F.ECoerc (F.FObj "outside") F.FInt _) -> pure ()
                result -> assertFailure (show result)
        , testCase "selected owner cannot be a lexical namesake" $
            rejects
                ( run
                    identityScheme
                    (F.mkEquation "f" [("x", F.FObj "alpha")] (F.EVar "x") (F.FObj "alpha"))
                    (F.fromListSEnv [("f", F.FFunc F.FInt F.FInt), ("value", F.FInt)])
                    [F.EVar "value"]
                )
        , testCase "shared formal coordinates reject inconsistent actual arguments" $
            rejects (run independentScheme repeatedEquation (F.fromListSEnv [("value", F.FInt), ("other", F.boolSort)]) [F.EVar "value", F.EVar "other"])
        , testCase "original result and arguments constrain one instance" $
            rejects
                ( run
                    identityScheme
                    (F.mkEquation "f" [("x", F.FObj "alpha")] F.PTrue F.boolSort)
                    (F.fromListSEnv [("value", F.FInt)])
                    [F.EVar "value"]
                )
        , testCase "a specialized result cannot solve a formed caller variable" $
            rejects
                ( run
                    identityScheme
                    (F.mkEquation "f" [("x", F.FObj "alpha")] (F.EVar "x") F.FInt)
                    (F.fromListSEnv [("value", F.FVar 7)])
                    [F.EVar "value"]
                )
        , testCase "opening the formals cannot capture a body-only indexed annotation" $ do
            let body coordinate = F.ECoerc (F.FVar 1) coordinate (F.EVar "x")
            case instanceAt identityScheme (F.FObj "alpha") F.FInt body of
                Right (F.ECoerc (F.FVar 1) F.FInt _) -> pure ()
                result -> assertFailure (show result)
        , testCase "real owner accepts an integer argument without changing its formal domain" $
            fmap SC.exprSortMaybe (numericInstance F.FReal Nothing)
                @?= Right (Just F.FReal)
        , testCase "integer owner keeps its intrinsic result under a real consumer" $
            fmap SC.exprSortMaybe (numericInstance F.FInt (Just F.FReal))
                @?= Right (Just F.FInt)
        , testCase "a function cast cannot replace the owner's intrinsic signature" $
            rejects
                ( SC.elabExprEAt
                    (C.solverFlags C.defConfig)
                    F.emptySymEnv{F.seSort = F.fromListSEnv [("f", F.FFunc F.FInt F.FInt)]}
                    mempty
                    "function annotation"
                    Nothing
                    (F.EApp (F.ECst (F.EVar "f") (F.FFunc F.FReal F.FReal)) (F.ECon (F.I 1)))
                )
        , testCase "a consumer cast cannot open a rigid nominal carrier" $
            rejects
                ( SC.elabExprEAt
                    (C.solverFlags C.defConfig)
                    F.emptySymEnv{F.seSort = F.fromListSEnv [("f", F.FObj "Native")]}
                    mempty
                    "nominal annotation"
                    Nothing
                    (F.ECst (F.EVar "f") (F.FObj "Other"))
                )
        , testCase "the cast smart constructor removes only redundant layers" $ do
            let source = F.ECst (F.EVar "x") F.FInt
                widened = F.ECst source F.FReal
            F.eCst source F.FInt @?= source
            F.eCst source F.FReal @?= widened
            F.eCst widened F.FReal @?= widened
        , testCase "nullary owner remains integer beneath an explicit real cast" $
            fmap
                SC.exprSortMaybe
                ( SC.instantiateEquationEAt
                    (C.solverFlags C.defConfig)
                    F.emptySymEnv{F.seSort = F.fromListSEnv [("f", F.FInt)]}
                    mempty
                    "nullary equation instantiation"
                    Nothing
                    (F.mkEquation "f" [] (F.ECst (F.ECon (F.I 1)) F.FInt) F.FInt)
                    (F.ECst (F.EVar "f") F.FReal)
                )
                @?= Right (Just F.FInt)
        , testCase "pinning the owner does not pin independent calls in its argument" $
            fmap
                SC.exprSortMaybe
                ( run
                    identityScheme
                    (F.mkEquation "f" [("x", F.FObj "alpha")] (identityBody (F.FObj "alpha")) (F.FObj "alpha"))
                    mempty
                    [independentArgument]
                )
                @?= Right (Just F.FInt)
        , testGroup
            "both engines retain the raw implicit-formal convention"
            [ testCase (show (interpreter, valid)) $
                withSystemTempDirectory "equation-engines" $ \path -> do
                    result <- Solver.solve (config path){C.interpreter = interpreter} (rawEquation valid)
                    assertResult (if valid then [] else [1]) result
            | interpreter <- [False, True]
            , valid <- [False, True]
            ]
        , testGroup
            "both engines preserve consumer conversion through composition"
            [ testCase (show (interpreter, name, valid)) $
                withSystemTempDirectory "equation-composed-engines" $ \path -> do
                    result <- Solver.solve (config path){C.interpreter = interpreter} query
                    assertResult (if valid then [] else [1]) result
            | interpreter <- [False, True]
            , valid <- [False, True]
            , (name, query) <- composedEquations valid
            ]
        , testGroup
            "both engines retain nullary and independent owner instances"
            [ testCase (show (interpreter, nullary, valid)) $
                withSystemTempDirectory "equation-owner-engines" $ \path -> do
                    result <- Solver.solve (config path){C.interpreter = interpreter} (ownerEquation nullary valid)
                    assertResult (if valid then [] else [1]) result
            | interpreter <- [False, True]
            , nullary <- [False, True]
            , valid <- [False, True]
            ]
        , testGroup
            "both engines preserve numeric owner and consumer distinctions"
            [ testCase (show (interpreter, realOwner, valid)) $
                withSystemTempDirectory "equation-numeric-engines" $ \path -> do
                    result <- Solver.solve (config path){C.interpreter = interpreter} (numericEquation realOwner valid)
                    assertResult (if valid then [] else [1]) result
            | interpreter <- [False, True]
            , realOwner <- [False, True]
            , valid <- [False, True]
            ]
        ]
  where
    identityScheme = F.mkFFunc 1 [F.FVar 0, F.FVar 0]
    independentScheme = F.mkFFunc 2 [F.FVar 0, F.FVar 1, F.FVar 0]
    identityBody coordinate = F.ECst (F.EVar "x") coordinate
    repeatedEquation = F.mkEquation "f" [("x", F.FObj "alpha"), ("y", F.FObj "alpha")] (F.EVar "x") (F.FObj "alpha")
    instanceAt scheme coordinate actual body =
        run
            scheme
            (F.mkEquation "f" [("x", coordinate)] (body coordinate) coordinate)
            (F.fromListSEnv [("value", actual)])
            [F.EVar "value"]
    run scheme equation bindings arguments =
        runExpected Nothing scheme equation bindings arguments
    runExpected expectation scheme equation bindings arguments =
        SC.instantiateEquationEAt
            (C.solverFlags C.defConfig)
            F.emptySymEnv{F.seSort = F.fromListSEnv [("f", scheme)]}
            bindings
            "equation instantiation"
            expectation
            equation
            (F.eApps (F.EVar "f") arguments)
    numericInstance carrier expectation =
        runExpected
            expectation
            (F.FFunc carrier carrier)
            (F.mkEquation "f" [("x", carrier)] (F.ECst (F.EVar "x") carrier) carrier)
            mempty
            [F.ECon (F.I 1)]
    numericEquation realOwner valid =
        queryWith [equation] [] [constraint 1 [] F.FInt F.PTrue goal]
      where
        carrier = if realOwner then F.FReal else F.FInt
        equation = F.mkEquation "f" [("x", carrier)] (F.ECst (F.EVar "x") carrier) carrier
        call = F.ECst (F.EApp (F.EVar "f") (F.ECon (F.I 1))) F.FReal
        goal = equal call (F.ECst (F.ECon (F.I (if valid then 1 else 2))) F.FReal)
    independentArgument =
        F.EIte
            (F.EApp (F.EVar "f") F.PTrue)
            (F.EApp (F.EVar "f") (F.ECon (F.I 1)))
            (F.ECon (F.I 2))
    ownerEquation nullary valid =
        (queryWith [equation] [] [constraint 1 [] F.FInt F.PTrue goal])
            { F.gLits = F.fromListSEnv [("f", if nullary then F.FInt else identityScheme)]
            }
      where
        equation =
            if nullary
                then F.mkEquation "f" [] (F.ECon (F.I 1)) F.FInt
                else F.mkEquation "f" [("x", F.FObj "alpha")] (F.EVar "x") (F.FObj "alpha")
        call =
            if nullary
                then F.ECst (F.EVar "f") F.FReal
                else F.EApp (F.EVar "f") independentArgument
        goal = equal call (F.ECst (F.ECon (F.I (if valid then 1 else 2))) (if nullary then F.FReal else F.FInt))
    composedEquations valid =
        [
            ( "outer real argument"
            , (base [] (equal (F.EApp (F.EVar "g") call) (F.EApp (F.EVar "g") wanted)))
                { F.gLits = F.fromListSEnv [("f", F.FFunc F.FInt F.FInt), ("g", F.FFunc F.FReal F.FReal)]
                }
            )
        , ("binary operand", base [] (equal (F.EBin F.Plus call (real one)) (real (integer (if valid then 2 else 3)))))
        ,
            ( "conditional branch"
            , (base [1] (equal (F.EIte (F.EVar "b") call (real two)) (F.EIte (F.EVar "b") wanted (real two))))
                { F.bs = F.bindEnvFromList [(1, ("b", reft F.boolSort F.PTrue, ()))]
                }
            )
        , ("lambda result", base [] (equal (F.ELam ("argument", F.FInt) call) (F.ELam ("other", F.FInt) wanted)))
        ]
      where
        integer = F.ECon . F.I
        one = integer 1
        two = integer 2
        real expression = F.ECst expression F.FReal
        call = real (F.EApp (F.EVar "f") one)
        wanted = real (if valid then one else two)
        equation = F.mkEquation "f" [("x", F.FInt)] (F.EVar "x") F.FInt
        base environment goal = queryWith [equation] [] [constraint 1 environment F.FInt F.PTrue goal]
    rejects result = case result of
        Left _ -> pure ()
        Right body -> assertFailure ("unsupported instance activated: " ++ show body)
    rawEquation valid =
        rr' "raw-equation" $
            unlines
                [ "constant f : func(1, [@(0); @(0); @(0)])"
                , "define f(x:alpha,y:alpha):alpha = { x }"
                , "constraint: env [] lhs {v:int | true} rhs {v:int | f true false = " ++ (if valid then "true" else "false") ++ "} id 1 tag []"
                , "expand [1 : True]"
                ]

sourceOnly :: Maybe (S.HashSet F.Symbol)
sourceOnly = Just S.empty

-- Both source lambdas return the same nominal sort. Only the positive
-- constructor field has that sort too. Match the normalizer's binder name so
-- its alpha-renaming cannot hide a term/type-coordinate collision from PLE.
nominalScopeQuery :: Bool -> F.FInfo ()
nominalScopeQuery valid =
    base
        { F.cm = M.singleton 1 (constraint 1 [] F.intSort F.PTrue goal)
        , F.gLits = F.insertSEnv "nominal_value" nominal (F.gLits base)
        , F.hoInfo = F.HOI True False
        }
  where
    nominal = F.FObj (F.lamArgSymbol 1)
    global = F.EVar "nominal_value"
    actual = if valid then global else F.PTrue
    call = F.ECst (F.EApp (F.EVar "prop") (F.EApp (F.EVar "Full") actual)) nominal
    goal = equal (F.ELam ("argument", F.boolSort) call) (F.ELam ("other", F.boolSort) global)
    base :: F.FInfo ()
    base =
        rr' "ple-nominal-scope" $
            unlines
                [ "data Box 1 = [ | Full {field : @(0)} ]"
                , "constant prop : func(2, [@(0); @(1)])"
                , "match prop Full x { x }"
                , "expand [1 : True]"
                ]

incompatibleMeasures :: [(String, F.FInfo ())]
incompatibleMeasures =
    [ ( name
      , rr' name $
            unlines
                [ "data Box 1 = [ | Empty {} | Full {field : @(0)} ]"
                , "constant prop : func(2, [@(0); @(1)])"
                , definition
                , wrapper
                , "constraint: env [] lhs {v:int | true} rhs {v:int | " ++ goal ++ "} id 1 tag []"
                , "expand [1 : True]"
                ]
      )
    | (name, definition, wrapper, goal) <-
        [ ("direct", "match prop Empty { Empty }", "", "prop (Empty : Box int)")
        , ("closed body", "match prop Empty { 0 }", "constant wrapped : func(0, [Box int; bool])\ndefine wrapped (x:Box int):bool = {prop x}", "wrapped (Empty : Box int)")
        , ("selector body", "match prop Full x { x }", "constant wrapped : func(0, [Box bool; int])\ndefine wrapped (x:Box bool):int = {prop x}", "wrapped (Full true) = 0")
        ]
    ]

proactiveNestedMeasure :: F.FInfo ()
proactiveNestedMeasure =
    rr' "proactive-nested" $
        unlines
            [ "data Inner 0 = [ | Full {field:int} ]"
            , "data Outer 0 = [ | Wrap {payload:int} ]"
            , "constant choose : func(0, [Inner; int])"
            , "constant observed : func(0, [Outer; int])"
            , "match choose Full x { x }"
            , "match observed Wrap x { choose (Full x) }"
            , "bind 1 x : {v:int | true}"
            , "bind 2 d : {v:Outer | v = Wrap x}"
            , "constraint: env [1;2] lhs {v:int | true} rhs {v:int | observed d = x} id 1 tag []"
            , "expand [1 : True]"
            ]

proactiveGrowthMeasure :: F.FInfo ()
proactiveGrowthMeasure =
    rr' "proactive-growth" $
        unlines
            [ "data Box 1 = [ | Full {field : @(0)} ]"
            , "constant grow : func(1, [Box @(0); Box (Box @(0))])"
            , "match grow Full x { Full (Full x) }"
            , "constraint: env [] lhs {v:int | true} rhs {v:int | grow (Full true) = Full (Full true)} id 1 tag []"
            , "expand [1 : True]"
            ]

proactiveRestrictedHelper :: F.FInfo ()
proactiveRestrictedHelper =
    rr' "proactive-source-authority" $
        unlines
            [ "data Unit 0 = [ | Empty {} ]"
            , "constant observed : func(0, [Unit; int])"
            , "constant some : func(0, [Unit; int])"
            , "constant restricted : func(0, [bool; int])"
            , "define restricted (b:bool):int = { if b then 0 else restricted b + 1 }"
            , "match observed Empty { restricted false }"
            , "bind 1 d : {v:Unit | v = Empty}"
            , "constraint: env [1] lhs {v:int | true} rhs {v:int | some d = some d + 1} id 1 tag []"
            , "expand [1 : True]"
            ]

-- The constructor argument fixes Box Int, independently of the demanded
-- Box Bool result. Replacing an equal local variable must retain both sorts.
measureQuery :: Bool -> Bool -> F.FInfo ()
measureQuery direct valid =
    rr' "measure-instance" $
        unlines
            [ "data Box 1 = [ | Empty {} | Full {field : @(0)} ]"
            , "constant prop : func(2, [@(0); @(1)])"
            , "match prop Empty { Empty }"
            , "bind 1 input : {v : Box int | v = Empty}"
            , "bind 2 result : {v : Box bool | v = prop " ++ argument ++ "}"
            , "constraint: env [1;2] lhs {v:int | true}"
            , "rhs {v:int | result = " ++ expected ++ "} id 1 tag []"
            , "expand [1 : True]"
            ]
  where
    argument = if direct then "(Empty : Box int)" else "input"
    expected = if valid then "Empty" else "Full true"

localShadowQuery :: Bool -> Bool -> F.FInfo ()
localShadowQuery = localShadowQueryAt "x" True

localShadowQueryAt :: F.Symbol -> Bool -> Bool -> Bool -> F.FInfo ()
localShadowQueryAt name includeFreeOccurrence letBound valid =
    queryWith
        [identity]
        [(1, name, reft F.intSort (equal value zero))]
        [constraint 1 [1] F.intSort F.PTrue (if includeFreeOccurrence then F.PAnd [equal (F.EVar name) zero, goal] else goal)]
  where
    identity = F.mkEquation "identity" [("argument", F.intSort)] (F.EVar "argument") F.intSort
    one = F.ECon (F.I 1)
    goal
        | letBound = equal (F.EApp (F.EVar "identity") (F.ELet name one (F.EVar name))) (if valid then one else zero)
        | otherwise =
            equal
                (F.ELam (name, F.intSort) (F.EVar name))
                (F.ELam ("y", F.intSort) (if valid then F.EVar "y" else zero))

withAuthority :: Maybe (S.HashSet F.Symbol) -> F.FInfo () -> F.FInfo ()
withAuthority authority query = query{F.ae = (F.ae query){F.aenvNative = authority}}

config :: FilePath -> C.Config
config path =
    C.defConfig
        { C.solver = C.Z3
        , C.srcFile = path ++ "/query.fq"
        , C.allowHO = True
        , C.rewriteAxioms = True
        , C.pleUndecGuards = True
        , C.extensionality = True
        , C.eliminate = C.Some
        }

check :: [Integer] -> Maybe (S.HashSet F.Symbol) -> F.FInfo () -> Assertion
check expected authority query = withSystemTempDirectory "ple-authority" $ \path -> do
    result <- Solver.solve (config path) (withAuthority authority query)
    assertResult expected result

assertResult :: [Integer] -> F.Result (Integer, ()) -> Assertion
assertResult expected result =
    case F.resStatus result of
        F.Safe _ -> expected @?= []
        F.Unsafe _ failures | not (null expected) -> sort (map fst failures) @?= expected
        failure -> assertFailure (show failure)

-- Exercise the actual saveQuery/solveFQ boundary, not just an in-memory codec.
-- An absent authority field on replay would turn the two negative cases SAFE.
replay :: [Integer] -> Maybe (S.HashSet F.Symbol) -> F.FInfo () -> Assertion
replay expected authority query = withSystemTempDirectory "ple-authority-replay" $ \path -> do
    let cfg = config path
    F.saveQuery cfg{C.save = True} (withAuthority authority query)
    mapM_
        ( \(format, loadQuery) -> do
            let filename = C.queryFile format cfg
            decoded <- loadQuery filename
            result <- Solver.solve cfg decoded
            assertResult expected result
            actual <- Solver.solveFQ cfg{C.srcFile = filename}
            actual @?= if null expected then ExitSuccess else ExitFailure 1
        )
        [ (Files.Fq, \filename -> rr' filename <$> readFile filename)
        , (Files.BinFq, \filename -> B.readFile filename >>= either (ioError . userError . show) pure . Store.decode)
        ]

queryWith :: [F.Equation] -> [(Int, F.Symbol, F.SortedReft)] -> [F.SubC ()] -> F.FInfo ()
queryWith equations bindings constraints =
    mempty
        { F.cm = M.fromList [(F.subcId obligation, obligation) | obligation <- constraints]
        , F.bs = F.bindEnvFromList [(index, (name, refinement, ())) | (index, name, refinement) <- bindings]
        , F.gLits =
            F.fromListSEnv
                [(F.eqName equation, foldr (F.FFunc . snd) (F.eqSort equation) (F.eqArgs equation)) | equation <- equations]
        , F.hoInfo = F.HOI True False
        , F.ae =
            mempty
                { F.aenvEqs = equations
                , F.aenvExpand = M.fromList [(F.subcId obligation, True) | obligation <- constraints]
                }
        }

constraint :: Integer -> [Int] -> F.Sort -> F.Expr -> F.Expr -> F.SubC ()
constraint identifier environment valueSort lhs rhs =
    F.mkSubC (F.fromListIBindEnv environment) (reft valueSort lhs) (reft valueSort rhs) (Just identifier) [] ()

reft :: F.Sort -> F.Expr -> F.SortedReft
reft valueSort predicate = F.RR valueSort (F.Reft ("v", predicate))

equal :: F.Expr -> F.Expr -> F.Expr
equal = F.PAtom F.Eq

zero, value, branch, guardedCall, guardedPredicate :: F.Expr
zero = F.ECon (F.I 0)
value = F.EVar "v"
branch = F.EVar "b"
guardedCall = F.EApp (F.EVar "guarded") branch
guardedPredicate = F.EIte branch (equal value guardedCall) F.PTrue

guardedEquation :: F.Equation
guardedEquation =
    F.Equ
        "guarded"
        [("b", F.boolSort)]
        (F.EIte branch zero (F.EBin F.Plus guardedCall (F.ECon (F.I 1))))
        F.intSort
        False

guardedGood, guardedPair, guardedSibling, guardedAssumption :: F.FInfo ()
guardedGood =
    queryWith
        [guardedEquation]
        [(0, "b", reft F.boolSort F.PTrue)]
        [constraint 1 [0] F.intSort (equal value zero) guardedPredicate]
guardedPair =
    guardedGood
        { F.bs =
            F.bindEnvFromList
                [(0, ("b", reft F.boolSort F.PTrue, ())), (1, ("branch", reft F.boolSort (F.PNot branch), ()))]
        , F.cm = M.insert 2 (constraint 2 [0, 1] F.intSort (equal value zero) F.PFalse) (F.cm guardedGood)
        , F.ae = (F.ae guardedGood){F.aenvExpand = M.fromList [(1, True), (2, True)]}
        }
guardedSibling =
    queryWith
        [guardedEquation]
        [(0, "b", reft F.boolSort F.PTrue)]
        [ constraint
            1
            [0]
            F.intSort
            (equal value zero)
            (F.PAnd [guardedPredicate, F.EIte branch F.PTrue F.PFalse])
        ]
guardedAssumption =
    queryWith
        [guardedEquation]
        [ (0, "b", reft F.boolSort F.PTrue)
        , (1, "fact", reft F.boolSort (equal (F.EIte branch (equal guardedCall zero) F.PTrue) F.PTrue))
        , (2, "branch", reft F.boolSort (F.PNot branch))
        ]
        [constraint 1 [0, 1, 2] F.intSort (equal value zero) F.PFalse]

inferredDemand :: F.FInfo ()
inferredDemand =
    ( queryWith
        [guardedEquation]
        [(0, "x", reft F.boolSort kvar), (1, "branch", reft F.boolSort (F.PNot (F.EVar "x")))]
        [ constraint 1 [] F.boolSort (F.PNot value) kvar
        , constraint 2 [0] F.boolSort (equal value (F.EVar "x")) kvar
        , constraint 3 [0, 1] F.intSort F.PTrue F.PFalse
        ]
    )
        { F.ws = M.singleton key (F.WfC (F.fromListIBindEnv []) [("v", F.boolSort)] (key) ())
        , F.quals = [F.mkQual "Partition" [F.QP "v" F.PatNone F.boolSort] partition (F.dummyPos "PLEAuthorityTests")]
        }
  where
    key = F.KV "k"
    kvar = F.PKVar key mempty mempty
    call = F.EApp (F.EVar "guarded") value
    partition = F.EIte (F.PAtom F.Gt call zero) F.PTrue (F.PAtom F.Le call zero)

-- The partial equations describe a source function admitted only at True.
-- Extensionality invents native-carrier applications; unfolding `first` must
-- not silently authorize the callback passed to it. The total mate differs
-- at True and requires native unfolding to establish function disequality.
callbackQuery :: Bool -> F.FInfo ()
callbackQuery partial =
    queryWith
        equations
        [(0, "b", reft F.boolSort (if partial then F.PNot value else value))]
        [constraint 1 [0] F.intSort F.PTrue (F.PAtom F.Ne (first "f") (first "g"))]
  where
    callbackSort = F.FFunc F.boolSort F.boolSort
    call = F.EApp (F.EVar "f") branch
    equations =
        [ F.Equ
            "f"
            [("b", F.boolSort)]
            (if partial then F.EIte branch F.PFalse (F.PNot call) else F.PFalse)
            F.boolSort
            False
        , F.Equ "g" [("b", F.boolSort)] (if partial then call else branch) F.boolSort False
        , F.Equ
            "first"
            [("k", callbackSort), ("b", F.boolSort)]
            (F.EApp (F.EVar "k") branch)
            F.boolSort
            False
        ]
    first name = F.EApp (F.EVar "first") (F.EVar name)
