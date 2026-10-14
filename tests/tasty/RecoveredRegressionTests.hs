{-# LANGUAGE OverloadedStrings #-}

-- | Regression tests of the old pushed fork (2a4c29fe..2d0f543f: 48640fdf,
-- eb836564, 2d0f543f, 27b0a229) that the consolidated tree dropped, ported to
-- the current API. Each still holds; the rest of the suite covers several of
-- them only partially (different entry point, sorts or solver), so they are
-- kept together here, grouped by the old commit whose meaning they guard.
--
-- Not carried over:
--
-- * 48640fdf pinned that the source checker (no native environment) admits
--   @Map ~~ int@ and @Set int ~~ Set bool@. Both still hold, but they record
--   head-only checking, not required behaviour; the native checker rejects
--   @Map ~~ int@ (below).
-- * 27b0a229's registry-merging and sort-nursery cases test an API
--   ('seValueInsts', 'pushAppls') that no longer exists; nested solver scopes
--   are covered by PolyFamilyTests.
-- * Nested integer division folding is covered by SimplifyTests
--   (Euclidean nested division).
module RecoveredRegressionTests (tests) where

import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad (void)
import Control.Monad.State (evalStateT, runState)
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.HashMap.Strict as M
import qualified Data.Text as T
import Data.List (isInfixOf)
import Data.Maybe (isJust)
import qualified Language.Fixpoint.Smt.Interface as SMT
import Language.Fixpoint.Smt.Serialize ()
import qualified Language.Fixpoint.Smt.Theories as Thy
import Language.Fixpoint.Smt.Types (Command (..), SMTLIB2, SmtM, runSmt2)
import Language.Fixpoint.SortCheck (ElabParam (..), Elaborate (..), checkSortExpr)
import Language.Fixpoint.Types
import Language.Fixpoint.Types.Config (Config (..), ElabFlags (..), SMTSolver (..), defConfig)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "recovered old-fork regressions" [sortCheck, binders, quantified, polyValue]

--------------------------------------------------------------------------------
-- 48640fdf: checkURel (source checker, no native environment)
--------------------------------------------------------------------------------

aggregate :: Symbol -> [Sort] -> Sort
aggregate c = fAppTC (symbolFTycon (dummyLoc c))

set, bag, array, mapt :: Sort
set = aggregate setConName [intSort]
bag = aggregate bagConName [intSort]
array = aggregate arrayConName [intSort, boolSort]
mapt = aggregate mapConName [intSort, intSort]

accepts :: Sort -> Brel -> Sort -> Bool
accepts s1 r s2 = isJust (checkSortExpr Nothing dummySpan env (PAtom r (EVar "x") (EVar "y")))
  where
    env = fromListSEnv [("x", s1), ("y", s2)]

acceptsNative :: Sort -> Brel -> Sort -> Bool
acceptsNative s1 r s2 = isJust (checkSortExpr (Just emptySymEnv) dummySpan env (PAtom r (EVar "x") (EVar "y")))
  where
    env = fromListSEnv [("x", s1), ("y", s2)]

both :: String -> Sort -> Sort -> Bool -> [TestTree]
both n s1 s2 expected = [testCase (n ++ " (" ++ show r ++ ")") (accepts s1 r s2 @?= expected) | r <- [Ueq, Une]]

sortCheck :: TestTree
sortCheck =
    testGroup "48640fdf checkURel" $
        concat
            [ both "Set ~~ int" set intSort False
            , both "Bag ~~ int" bag intSort False
            , both "Array ~~ int" array intSort False
            , both "int ~~ Set" intSort set False
            , both "Set ~~ Bag" set bag False
            , both "Set ~~ Array" set array False
            , both "Bag ~~ Array" bag array False
            , both "Set ~~ Set" set set True
            , both "Bag ~~ Bag" bag bag True
            , both "Array ~~ Array" array array True
            , both "int ~~ int" intSort intSort True
            , both "bool ~~ bool" boolSort boolSort True
            , both "Map ~~ Map" mapt mapt True
            , both "Array/1 ~~ int" (aggregate arrayConName [intSort]) intSort True
            ]
            ++ [ testCase "int ~~ bool" (accepts intSort Ueq boolSort @?= False)
               , testCase "native: Map ~~ int rejected" (acceptsNative mapt Ueq intSort @?= False)
               , testCase "native: Set ~~ int rejected" (acceptsNative set Ueq intSort @?= False)
               , testCase "native: Map ~~ same-carrier Array admitted" (acceptsNative mapt Ueq (arraySort intSort intSort) @?= True)
               ]

--------------------------------------------------------------------------------
-- eb836564: binders and body casts are judged in one representation
--------------------------------------------------------------------------------

binders :: TestTree
binders =
    testGroup
        "eb836564 binder normalization"
        [ testGroup
            "accepted with matching body casts"
            [ testCase (bn ++ "/" ++ sn ++ "/arrays=" ++ show arrays) $ do
                let ef = ElabFlags arrays False
                    body = PAtom Eq (ECst (EVar "x") s) (EVar "x")
                    result = elaborate (ElabParam ef "binder regression" emptySymEnv) (bind s body)
                _ <- evaluate (length (show result))
                checkSortExpr Nothing dummySpan emptySEnv result @?= Just (resultSort s)
            | (bn, bind, resultSort) <- binderForms
            , (sn, s) <- binderSorts
            , arrays <- [False, True]
            ]
        , testGroup
            "valid in the solver under both set representations"
            [ testCase (sn ++ "/arrays=" ++ show arrays) $ do
                let ef = ElabFlags arrays False
                    x = EVar "x"
                    claim = PNot (PAll [("x", s)] (PAtom Eq x (ECst x s)))
                    elaborated = elaborate (ElabParam ef "binder solver" emptySymEnv) claim
                    config = defConfig{solver = if arrays then Z3 else Cvc5}
                unsat <-
                    bracket
                        (SMT.makeContextWithSEnv config "binder-solver" emptySymEnv mempty)
                        SMT.cleanupContext
                        (\context -> flip evalStateT context (SMT.smtAssert elaborated >> SMT.smtCheckUnsat))
                unsat @?= True
            | (sn, s) <- binderSorts
            , arrays <- [False, True]
            ]
        , testGroup
            "rejected genuine cast mismatches"
            [ testCase (bn ++ "/" ++ cn ++ "/arrays=" ++ show arrays) $ do
                let body = PAtom Eq (ECst (EVar "x") target) (EVar "x")
                    result = elaborate (ElabParam (ElabFlags arrays False) "bad binder cast" emptySymEnv) (bind source body)
                outcome <- try (evaluate (length (show result))) :: IO (Either SomeException Int)
                case outcome of
                    Left err -> assertBool (show err) ("incompatible sort" `isInfixOf` show err)
                    Right _ -> assertFailure "elaboration admitted an incompatible array cast"
            | (bn, bind, _) <- binderForms
            , (cn, source, target) <- badCasts
            , arrays <- [False, True]
            ]
        ]
  where
    binderForms :: [(String, Sort -> Expr -> Expr, Sort -> Sort)]
    binderForms =
        [ ("lambda", \s -> ELam ("x", s), \s -> FFunc s boolSort)
        , ("forall", \s -> PAll [("x", s)], const boolSort)
        , ("exists", \s -> PExist [("x", s)], const boolSort)
        ]
    binderSorts =
        [ ("set", set)
        , ("bag", bag)
        , ("map", mapt)
        , ("array", array)
        , ("nested-set", setSort (setSort intSort))
        , ("nested-map", aggregate mapConName [set, bag])
        , ("nested-array", arraySort set bag)
        ]
    badCasts =
        [ ("wrong-array-range", array, arraySort intSort intSort)
        , ("wrong-array-element", array, arraySort boolSort boolSort)
        , ("array-to-int", array, intSort)
        ]

--------------------------------------------------------------------------------
-- 2d0f543f: vacuous family quantifiers and triggered binder scope
--------------------------------------------------------------------------------

qScheme :: Sort
qScheme = FAbs 0 (FVar 0)

qEnv :: SymEnv
qEnv = emptySymEnv{seSort = fromListSEnv [("family", qScheme)]}

render :: (SMTLIB2 a) => SymEnv -> a -> (String, SymEnv)
render env expression = (BS.unpack (toLazyByteString output), final)
  where
    (output, final) = runState (runSmt2 expression) env

integer :: Symbol -> Expr
integer name = ECst (EVar name) intSort

identity :: Symbol -> Expr
identity name = PAtom Eq (integer name) (integer name)

rejectsIn :: (SMTLIB2 a) => SymEnv -> String -> a -> Assertion
rejectsIn env message expression = do
    outcome <- try (evaluate (length (fst (render env expression)))) :: IO (Either SomeException Int)
    case outcome of
        Left exception -> assertBool (show exception) (message `isInfixOf` show exception)
        Right _ -> assertFailure "unsupported family expression was serialized"

rejectsFamily :: (SMTLIB2 a) => a -> Assertion
rejectsFamily = rejectsIn qEnv "quantified polymorphic value families are not supported"

preserves :: Expr -> Expr -> Assertion
preserves original simplified = do
    fst (render qEnv original) @?= fst (render qEnv simplified)
    seSort (snd (render qEnv original)) @?= seSort qEnv

-- The old fork's default trigger was the left-hand side of the body; upstream
-- removed implicit triggers, so the ported controls spell the pattern out.
lhsTrigger :: Expr -> Triggered Expr
lhsTrigger p = TR (Patterns [[lhs (body p)]]) p
  where
    body (PAll _ b) = b
    body (PExist _ b) = b
    body b = b
    lhs (PAtom _ l _) = l
    lhs e = e

solverIn :: SymEnv -> String -> SmtM a -> IO a
solverIn env name action =
    bracket (SMT.makeContextWithSEnv defConfig name env mempty) SMT.cleanupContext (evalStateT action)

quantified :: TestTree
quantified =
    testGroup
        "2d0f543f quantified families"
        [ testGroup
            "dropping an unused family preserves the body"
            [ testCase (qn ++ " " ++ tn) $ do
                let expression = quantifier [("family", qScheme)] body
                preserves expression body
                actual <- solverIn qEnv "qf-truth" (SMT.smtAssert expression >> SMT.smtCheckUnsat)
                actual @?= expectedUnsat
            | (qn, quantifier) <- [("exists", PExist), ("forall", PAll)]
            , (tn, body, expectedUnsat) <- [("true", PTrue, False), ("false", PFalse, True)]
            ]
        , testGroup
            "used family binders still reject"
            [testCase qn $ rejectsFamily (quantifier [("family", qScheme)] (identity "family")) | (qn, quantifier) <- [("exists", PExist), ("forall", PAll)]]
        , testCase "triggered used family still rejects" $
            rejectsFamily (lhsTrigger (PAll [("family", qScheme)] (identity "family")))
        , testCase "unused lambda family still rejects" $
            rejectsFamily (ELam ("family", qScheme) (ECst PTrue boolSort) :: Expr)
        , testCase "remaining monomorphic binder is preserved" $ do
            let body = identity "ordinary"
            preserves (PAll [("family", qScheme), ("ordinary", intSort)] body) (PAll [("ordinary", intSort)] body)
        , testCase "nested quantifier shadows the outer family" $ do
            let inner = PAll [("family", intSort)] (identity "family")
            preserves (PExist [("family", qScheme)] inner) inner
        , testCase "nested shadow does not hide a sibling outer use" $
            rejectsFamily (PExist [("family", qScheme)] (PAnd [PAll [("family", intSort)] (identity "family"), identity "family"]))
        , testCase "let binder shadows family only in its body" $ do
            let inner = ELet "family" (ECon (I 0)) (identity "family")
            preserves (PExist [("family", qScheme)] inner) inner
        , testCase "let initializer still uses the outer family" $
            rejectsFamily (PExist [("family", qScheme)] (ELet "family" (integer "family") (identity "family")))
        , testGroup
            "unsupported type syntax cannot hide a family use"
            [ testCase n $ rejectsFamily (PExist [("family", qScheme)] body)
            | (n, body) <-
                [ ("ETApp", ETApp (identity "family") intSort)
                , ("ETAbs", ETAbs (identity "family") "a")
                , ("same-spelling type binder", ETAbs (identity "family") "family")
                ]
            ]
        , testCase "KVar substitution cannot hide a family use" $
            rejectsFamily (PExist [("family", qScheme)] (PKVar (KV "k") mempty (toKVarSubst (M.singleton "argument" (integer "family")))))
        , testCase "pruned triggered quantifier retains its body" $ do
            let body = PAtom Eq (ECon (I 0)) (ECon (I 0)) :: Expr
            fst (render qEnv (lhsTrigger (PAll [("family", qScheme)] body))) @?= fst (render qEnv body)
        , testCase "pruned triggered existential retains false" $ do
            let axiom = TR (Patterns []) (PExist [("family", qScheme)] PFalse :: Expr)
            fst (render qEnv axiom) @?= fst (render qEnv (PFalse :: Expr))
            actual <- solverIn qEnv "qf-axiom" (SMT.smtAssertAxiom axiom >> SMT.smtCheckUnsat)
            actual @?= True
        , testCase "trigger patterns are rendered in the binder's own scope" $ do
            -- The body and its pattern must name the SAME bound variable; a
            -- pattern rendered outside the binder sees the global family.
            let apply = EApp (EVar "f")
                body = PAtom Eq (apply (integer "family")) (integer "family")
                output = fst (render qEnv (TR (Patterns [[apply (integer "family")]]) (PAll [("family", intSort)] body)))
                bound = takeWhile (\ch -> ch /= ' ' && ch /= ')') (dropWhile (/= '_') (snd (breakOn "((_lq_bound_" output)))
                breakOn needle hay = case [i | i <- [0 .. length hay - length needle], take (length needle) (drop i hay) == needle] of
                    (i : _) -> splitAt i hay
                    [] -> (hay, "")
            assertBool output (not (null bound))
            assertBool output ((":pattern((" ++ T.unpack (symbolSmtText "f") ++ " " ++ bound ++ ")") `isInfixOf` output)
        , testGroup
            "ordinary binders shadow global families in body and trigger"
            [ testCase n $ do
                let apply = EApp (EVar "f")
                    axiom = PAll bs (PAtom Eq (apply (integer "family")) (integer "family"))
                actual <- solverIn qEnv "qf-trigger" $ do
                    SMT.smtFuncDecl (symbolSmtText "f") ([SInt], SInt)
                    if triggered then SMT.smtAssertAxiom (lhsTrigger axiom) else SMT.smtAssert axiom
                    before <- SMT.smtCheckUnsat
                    SMT.smtAssert (PAtom Ne (apply (ECon (I 1))) (ECon (I 1)))
                    after <- SMT.smtCheckUnsat
                    pure (before, after)
                actual @?= (False, True)
            | (n, bs, triggered) <-
                [ ("plain", [("family", intSort)], False)
                , ("trigger", [("family", intSort)], True)
                , ("trigger after unused family removal", [("unused", qScheme), ("family", intSort)], True)
                ]
            ]
        ]

--------------------------------------------------------------------------------
-- 27b0a229: polymorphic value identity (behavioral cases only)
--------------------------------------------------------------------------------

pScheme, integers, tokens, generic :: Sort
pScheme = FAbs 0 (arraySort (FVar 0) boolSort)
integers = arraySort intSort boolSort
tokens = arraySort token boolSort
generic = arraySort (FObj "a") boolSort

token :: Sort
token = fAppTC (symbolFTycon (dummyLoc "Token")) []

pEnv :: SymEnv
pEnv =
    emptySymEnv
        { seSort = fromListSEnv [("family", pScheme), ("other", pScheme)]
        , seData = fromListSEnv [("Token", DDecl (symbolFTycon (dummyLoc "Token")) 0 [DCtor (dummyLoc "First") [], DCtor (dummyLoc "Second") []])]
        }

value :: Symbol -> Sort -> Expr
value name = ECst (EVar name)

polyValue :: TestTree
polyValue =
    testGroup
        "27b0a229 polymorphic values"
        [ testCase "different actual result sorts render differently" $ do
            let (first, env) = render pEnv (value "family" tokens)
            assertBool first (fst (render env (value "family" integers)) /= first)
        , testCase "generic-sort erasure shares the concrete instance" $ do
            let (first, env) = render pEnv (value "family" generic)
            fst (render env (value "family" integers)) @?= first
        , testCase "residual FAbs target rejects" $
            rejectsIn pEnv "uninstantiated polymorphic value family" (value "family" pScheme)
        , testCase "recursive function sort normal forms share an instance" $ do
            let direct = arraySort (FFunc intSort boolSort) boolSort
                elaborated = arraySort (FApp (FApp funcSort intSort) boolSort) boolSort
                (first, env) = render pEnv (value "family" direct)
            fst (render env (value "family" elaborated)) @?= first
            normalizeValueInstance direct @?= normalizeValueInstance elaborated
        , testCase "nested function and Int instances remain distinct" $ do
            let (first, env) = render pEnv (value "family" integers)
            assertBool first (fst (render env (value "family" (arraySort (FFunc intSort intSort) boolSort))) /= first)
        , testCase "ordinary polymorphic functions remain defunctionalized functions" $ do
            let env = insertSymEnv "function" (FAbs 0 (FFunc (FVar 0) (FVar 0))) pEnv
            polyValueSort env "function" @?= Nothing
        , testCase "authoritative native theory symbols do not become family tags" $ do
            let env = pEnv{seSort = insertSEnv Thy.setEmpty pScheme (seSort pEnv), seTheory = Thy.theorySymbols Z3}
            assertBool "missing native empty-set theory classification" $
                case symEnvTheory Thy.setEmpty env of
                    Just entry -> tsInterp entry == Theory
                    Nothing -> False
            polyValueSort env Thy.setEmpty @?= Nothing
        , testCase "true nullary datatype constructors keep as syntax" $ do
            -- "List" is the built-in list tycon (symbol "[]"); use a plain one.
            let constructor = symbolFTycon (dummyLoc "Lst")
                datatype = DDecl constructor 1 [DCtor (dummyLoc "Nil") []]
                env =
                    pEnv
                        { seSort = insertSEnv "Nil" (FAbs 0 (fAppTC constructor [FVar 0])) (seSort pEnv)
                        , seTheory = Thy.theorySymbols [datatype]
                        , seData = insertSEnv (symbol constructor) datatype (seData pEnv)
                        }
            polyValueSort env "Nil" @?= Nothing
            let output = fst (render env (value "Nil" (fAppTC constructor [token])))
                prefix = "(as " ++ T.unpack (symbolSmtText "Nil") ++ " "
            assertBool output (prefix `isInfixOf` output && not (" Int)" `isInfixOf` output))
        , testCase "polymorphic quantifier rejects explicitly" $
            rejectsIn pEnv "quantified polymorphic value families" (PAll [("local", pScheme)] (PAtom Eq (value "local" integers) (value "local" integers)) :: Expr)
        , testCase "polymorphic lambda binder rejects explicitly" $
            rejectsIn pEnv "quantified polymorphic value families" (ELam ("local", pScheme) (ECst PTrue boolSort) :: Expr)
        , testGroup
            "monomorphic binders shadow global family schemes"
            [ testCase n $ do
                let (output, final) = render pEnv expression
                assertBool output (not ("apply" `isInfixOf` output))
                seSort final @?= seSort pEnv
            | let body = PAtom Eq (value "family" intSort) (value "family" intSort)
            , (n, expression) <-
                [ ("forall", PAll [("family", intSort)] body)
                , ("exists", PExist [("family", intSort)] body)
                , ("let", ELet "family" (ECon (I 0)) body)
                , ("lambda", ELam ("family", intSort) (ECst body boolSort))
                ]
            ]
        , testCase "define-fun arguments shadow global family schemes" $ do
            let body = PAtom Eq (value "family" integers) (value "family" integers)
                (output, final) = render pEnv (DefineFunc "test" [("family", SArray SInt SBool)] SBool body)
            assertBool output (not ("apply" `isInfixOf` output))
            seSort final @?= seSort pEnv
        , testGroup
            "solver declarations precede first family use"
            [ testCase n $ do
                let left = value "family" tokens
                    right = value "other" tokens
                (satisfiable, contradictory) <- solverIn pEnv "polyvalue-probe" $ do
                    firstAssertion (PAtom Ne left right)
                    first <- SMT.smtCheckUnsat
                    SMT.smtAssert (PAtom Eq left right)
                    second <- SMT.smtCheckUnsat
                    pure (first, second)
                satisfiable @?= False
                contradictory @?= True
            | (n, firstAssertion) <-
                [ ("ordinary assert", SMT.smtAssert)
                , ("axiom", SMT.smtAssertAxiom . noTrigger)
                , ("distinct", \_ -> SMT.smtDistinct [value "family" tokens, value "other" tokens])
                , ("direct command", void . SMT.command . Assert Nothing)
                ,
                    ( "define-fun body"
                    , \_ -> do
                        SMT.smtDefineFunc "definedValue" [] tokens (value "family" tokens)
                        SMT.smtAssert (PAtom Ne (EVar "definedValue") (value "other" tokens))
                    )
                ]
            ]
        ]
