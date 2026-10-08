{-# LANGUAGE OverloadedStrings #-}

module SmtScopeTests (tests) where

import Control.DeepSeq (force)
import Control.Exception (SomeException, bracket, evaluate, try)
import Control.Monad.State (evalState, evalStateT, modify, runState)
import Data.ByteString.Builder (intDec, toLazyByteString)
import qualified Data.ByteString.Lazy.Char8 as B
import Data.Char (ord)
import qualified Data.HashMap.Strict as M
import Data.List (isInfixOf, nub)
import qualified Data.Store as Store
import qualified Data.Text as T
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Serialize ()
import qualified Language.Fixpoint.Smt.Theories as Thy
import qualified Language.Fixpoint.Solver.Common as Common
import qualified Language.Fixpoint.SortCheck as Check
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as Config
import qualified Language.Fixpoint.Types.Names as N
import qualified SMTLIB.Backends as Backend
import SortInventoryTests (allocationBytes)
import System.Process (readProcess)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

tests :: TestTree
tests = testGroup "SMT scope and observations" [lexicalTests, namesTests, publicTests, modelTests, valuesTests, standaloneTests]

lexicalTests :: TestTree
lexicalTests =
    testGroup
        "lexical SMT names"
        [ testCase "contextual query locals cannot define nominal sorts" $
            bracket (SMT.makeContextNoLog Config.defConfig) SMT.cleanupContext $ \context ->
                mapM_
                    ( \annotation -> do
                        let expression = F.ECst F.PTrue annotation
                            lowered = Common.toSMT "lexical sort ownership" Config.defConfig context [("alpha", F.boolSort)] expression
                        result <- try (evaluate (force lowered)) :: IO (Either SomeException F.Expr)
                        case result of
                            Left failure -> do
                                annotation @?= F.FObj "alpha"
                                assertBool (show failure) ("elaborate" `isInfixOf` show failure)
                            Right _ -> annotation @?= F.boolSort
                    )
                    [F.boolSort, F.FObj "alpha"]
        , testGroup
            "closed binder ignores global theory alias"
            [ testCase label $ lexicalRender lexicalDecorated expression @?= lexicalRender mempty expression
            | (label, expression) <-
                [ ("universal", F.PAll [("x", F.intSort)] lexicalReflexive)
                , ("existential", F.PExist [("x", F.intSort)] lexicalReflexive)
                , ("nested shadowing", F.PAll [("x", F.intSort)] (F.PExist [("x", F.boolSort)] (F.EVar "x")))
                , ("let", F.ELet "x" (F.ECon (F.I 3)) lexicalReflexive)
                , ("cast", F.PAll [("x", F.intSort)] (lexicalEqual (F.ECst (F.EVar "x") F.intSort) (F.EVar "x")))
                , ("lambda placeholder", F.ELam ("x", F.intSort) (F.ECst (F.EVar "x") F.intSort))
                , ("captured outer binder in lambda", F.PAll [("x", F.intSort)] (lexicalEqual (F.ELam ("y", F.intSort) (F.ECst (F.EVar "x") F.intSort)) (F.ELam ("y", F.intSort) (F.ECst (F.EVar "x") F.intSort))))
                ]
            ]
        , testCase "free theory reference remains native" $
            lexicalRender lexicalDecorated (F.EVar "x" :: F.Expr) @?= "true"
        , testCase "native reserved operator remains raw" $ do
            let environment = mempty{F.seTheory = F.fromListSEnv [("not", F.Thy "not" "not" (F.FFunc F.boolSort F.boolSort) F.Theory)]}
            lexicalRender environment (F.EVar "not" :: F.Expr) @?= "not"
            lexicalRender environment (F.PAll [("not", F.boolSort)] (F.EVar "not") :: F.Expr) @?= "(forall ((_lq_bound_0 Bool)) _lq_bound_0)"
        , testCase "declared equation uses escaped rather than native spelling" $ do
            let equation = F.Equ "not" [("true", F.boolSort)] (F.EVar "true") F.boolSort False :: F.Equation
                environment = mempty{F.seTheory = F.theorySymbols [equation]}
                definition = SMT.DefineFunc "not" [("true", F.SBool)] F.SBool (F.EVar "true")
            lexicalRender environment definition @?= "(define-fun key$not ((_lq_bound_0 Bool)) Bool _lq_bound_0)"
        , testCase "let initializer observes outer binding" $
            lexicalRender lexicalDecorated (F.ELet "x" (F.EVar "x") (F.EVar "x") :: F.Expr) @?= "(let ((_lq_bound_0 true)) _lq_bound_0)"
        , testCase "lexical scope does not leak to sibling" $
            lexicalRender lexicalDecorated (F.PAnd [F.PAll [("x", F.intSort)] lexicalReflexive, F.EVar "x"])
                @?= "(and (forall ((_lq_bound_0 Int)) (= _lq_bound_0 _lq_bound_0)) true)"
        , testCase "define-fun parameters ignore global theory aliases" $
            lexicalRender lexicalDecorated lexicalDefinition @?= lexicalRender mempty lexicalDefinition
        , testCase "trigger and body share bound coordinates" $
            lexicalRender lexicalDecorated lexicalTriggered @?= lexicalRender mempty lexicalTriggered
        , testCase "hard-coded native application is shadowed" $ do
            let name = Thy.setEmpty
                expression =
                    F.PAll
                        [(name, F.FFunc F.intSort F.intSort)]
                        (lexicalEqual (F.EApp (F.ECst (F.EVar name) (F.FFunc F.intSort F.intSort)) (F.ECon (F.I 1))) (F.ECon (F.I 1)))
                output = lexicalRender mempty expression
            assertBool output (not ("as set.empty" `isInfixOf` output))
        , testCase "function-tag allocation survives a lexical body" $ do
            let expression =
                    F.PAll
                        [("x", F.intSort)]
                        ( lexicalEqual
                            (F.ELam ("y", F.intSort) (F.ECst (F.EVar "x") F.intSort))
                            (F.ELam ("y", F.intSort) (F.ECst (F.EVar "x") F.intSort))
                        )
                (_, final) = runState (SMT.smt2 expression) lexicalDecorated
            assertBool "lambda tag was discarded" (F.seIx final > F.seIx lexicalDecorated)
            F.seTheory final @?= F.seTheory lexicalDecorated
        , testGroup
            "instance allocation precedes a lexical binder"
            [ testCase label $ modelWithContext $ \context -> do
                let value = F.ECst (F.EVar "f") F.boolSort
                    expression = F.ELet (F.intSymbol "lq_instantiated_value" (0 :: Int)) (F.PNot value) value
                    environment = mempty{F.seSort = F.fromListSEnv [("f", F.FAbs 0 (F.FVar 0))]}
                result <-
                    evalStateT
                        ( do
                            modify (\current -> current{SMT.ctxSymEnv = environment})
                            SMT.smtAssert (F.PNot (F.PIff expression (expectedValue value)))
                            SMT.command SMT.CheckSat
                        )
                        context
                result @?= expected
            | (label, expectedValue, expected) <-
                [ ("unused let preserves the selected global", id, SMT.Unsat)
                , ("unused let cannot negate the selected global", F.PNot, SMT.Sat)
                ]
            ]
        , testCase "nested ordinary application serializes each argument once" $ do
            let depth = 16
                expression = iterate (F.EApp (F.EVar "f")) (F.ECon (F.I 0)) !! depth :: F.Expr
                environment = mempty{F.seSort = F.fromListSEnv [("f", F.FFunc F.intSort F.intSort)]}
                output = lexicalRender environment expression
            _ <- evaluate (force (expression, environment))
            bytes <- allocationBytes output
            output @?= concat (replicate depth "(key$f ") ++ "0" ++ replicate depth ')'
            assertBool ("repeated argument serialization allocated " ++ show bytes) (bytes < 4 * 1024 * 1024)
        , testCase "ordinary underscore application keeps a function-valued argument" $ do
            let arrow = F.FFunc F.boolSort F.boolSort
                environment =
                    mempty
                        { F.seSort = F.fromListSEnv [("_", F.FFunc arrow F.boolSort), ("nativeNot", arrow)]
                        , F.seTheory = F.fromListSEnv [("nativeNot", F.Thy "nativeNot" "not" arrow F.Theory)]
                        }
                expression = F.EApp (F.EVar "_") (F.EVar "nativeNot") :: F.Expr
                (builder, final) = runState (SMT.smt2 expression) environment
                output = B.unpack (toLazyByteString builder)
            length (F.seInstancesCur final) @?= 1
            assertBool output ("key$lq_instantiated_value" `isInfixOf` output && not (" not)" `isInfixOf` output))
        , testGroup
            "instance declarations have fresh identifier tokens"
            [ testCase label $ do
                let tag i = F.intSymbol "lq_instantiated_value" (i :: Int)
                    environment =
                        mempty
                            { F.seSort = F.fromListSEnv (("f", F.FAbs 0 (F.FVar 0)) : [(name, F.FInt) | name <- occupied tag])
                            , F.seTheory = F.fromListSEnv [("alias", F.Thy "alias" (raw (F.symbolSmtText (tag 0))) F.FInt F.Theory)]
                            }
                    (builder, final) = runState (SMT.smt2 (F.ECst (F.EVar "f") F.FInt :: F.Expr)) environment
                B.unpack (toLazyByteString builder) @?= T.unpack (F.symbolSmtText (tag expected))
                F.seIx final @?= expected + 1
            | (label, occupied, raw, expected) <-
                [ ("ordinary declaration collision", \tag -> [tag 0, tag 1], const "unrelated", 2)
                , ("identifier substrings are not collisions", \tag -> [F.suffixSymbol (tag 0) "suffix"], const "unrelated", 0)
                , ("quoted raw alias collision", const [], \name -> "|" <> name <> "|", 1)
                , ("compound raw alias collision", const [], \name -> "(+ " <> name <> " 1)", 1)
                ]
            ]
        , testGroup
            "serialization does not enumerate unrelated declarations"
            [ testCase label $ do
                let functions = [F.intSymbol "function" i | i <- [1 .. 64 :: Int]]
                    sorts = [(F.intSymbol "ordinary" i, F.FObj (F.intSymbol "kind" i)) | i <- [1 .. 16384 :: Int]] ++ [(name, F.FAbs 0 (F.FVar 0)) | name <- functions]
                    environment = mempty{F.seSort = F.fromListSEnv sorts}
                    expressions = [enclose (F.ECst (F.EVar name) F.FInt) | name <- functions] :: [F.Expr]
                    output = B.unpack (toLazyByteString (mconcat (evalState (mapM SMT.smt2 expressions) environment)))
                _ <- evaluate (force (environment, expressions))
                bytes <- allocationBytes output
                assertBool ("ambient declaration enumeration allocated " ++ show bytes) (bytes < 8 * 1024 * 1024)
            | (label, enclose) <-
                [ ("instances", id)
                , ("lexical binders", \value -> F.PAll [("bound", F.FInt)] (lexicalEqual value value))
                ]
            ]
        , testGroup
            "deferred instance sorts belong to declarations, not term binders"
            [ testCase label $ do
                let native = Thy.theorySymbols Config.Z3
                    environment = mempty{F.seSort = F.fromListSEnv declarations <> fmap F.tsSort native, F.seTheory = native}
                    function index = F.FFunc F.boolSort (F.arraySort index F.boolSort)
                    occurrence index = F.ECst (F.EVar Thy.arrConstM) (function index)
                    expression = F.PAll [("alpha", lexicalKind)] (lexicalEqual (occurrence (F.FObj "alpha")) (occurrence expected))
                    (_, final) = runState (SMT.smt2 expression) environment
                M.keys (F.seInstancesCur final) @?= [(Thy.arrConstM, function expected)]
                F.seSort final @?= F.seSort environment
                F.sortSmtSort False final (F.arraySort expected F.boolSort) @?= F.SArray carrier F.SBool
            | (label, declarations, lexicalKind, expected, carrier) <-
                [ ("numeric alias", [("alpha", F.FFrac)], F.FNum, F.FReal, F.SReal)
                , ("rigid nominal", [], F.FFrac, F.FObj "alpha", F.SInt)
                ]
            ]
        , testCase "indexed operator tokens follow the native declaration" $ do
            let theory = Check.theoryEnv Config.defConfig (mempty :: F.SInfo ())
            case F.lookupSEnv "_" theory of
                Nothing -> assertBool "missing indexed-operator declaration" False
                Just declaration -> do
                    let native = F.insertSEnv "indexAlias" declaration theory
                        environment = mempty{F.seSort = F.tsSort <$> native, F.seTheory = native}
                        expression name = F.eApps (F.ECst (F.EVar name) (F.tsSort declaration)) [F.EVar "zero_extend", F.expr (2 :: Integer)]
                    mapM_ (\name -> lexicalRender environment (expression name) @?= "(_ zero_extend 2)") ["_", "indexAlias"]
        , testGroup
            "free native alias under an unrelated binder"
            [ testCase label $ do
                let raw = "_lq_bound_0"
                    environment = mempty{F.seTheory = F.fromListSEnv [("y", F.Thy "y" (T.pack raw) F.boolSort F.Theory)]}
                    script = "(set-logic ALL)\n(declare-fun " ++ raw ++ " () Bool)\n(assert " ++ raw ++ ")\n(assert (not " ++ lexicalRender environment (expression :: F.Expr) ++ "))\n(check-sat)\n"
                result <- readProcess z3 ["-in"] script
                result @?= expected
            | (label, expression, expected) <-
                [ ("global truth is independent of the bound value", F.PAll [("x", F.boolSort)] (F.EVar "y"), "unsat\n")
                , ("bound value need not equal free global alias", F.PAll [("x", F.boolSort)] (F.PIff (F.EVar "x") (F.EVar "y")), "sat\n")
                ]
            ]
        , testGroup
            "freshening protects all rendered coordinates"
            [ testCase label $ do
                let raw = "_lq_bound_0"
                    alias = aliasText raw
                    next = F.intSymbol ("x" :: F.Symbol) (0 :: Int)
                    environment = mempty{F.seTheory = F.fromListSEnv [("y", F.Thy "y" (T.pack alias) F.boolSort F.Theory)]}
                    script = "(set-logic ALL)\n(declare-fun " ++ raw ++ " () Bool)\n(declare-fun " ++ lexicalIdentifier next ++ " () Bool)\n(assert " ++ assumption raw ++ ")\n(assert " ++ lexicalIdentifier next ++ ")\n" ++ lexicalRenderScript environment expression ++ "\n(check-sat)\n"
                result <- readProcess z3 ["-in"] script
                result @?= "unsat\n"
            | (label, aliasText, assumption, expression) <-
                [ ("a used fresh-looking global is not captured", id, id, \_ -> F.PAll [("x", F.boolSort)] (F.PAnd [F.EVar "y", F.EVar (F.intSymbol ("x" :: F.Symbol) (0 :: Int))]))
                , ("nested binder cannot capture renamed outer binder", id, id, \_ -> F.PAll [("x", F.boolSort)] (F.PExist [(F.intSymbol ("x" :: F.Symbol) (0 :: Int), F.boolSort)] (F.PAnd [F.EVar "y", F.PNot (F.PIff (F.EVar "x") (F.EVar (F.intSymbol ("x" :: F.Symbol) (0 :: Int))))])))
                , ("quoted alias is protected", \raw -> "|" ++ raw ++ "|", id, \_ -> F.PAll [("x", F.boolSort)] (F.EVar "y"))
                , ("identifier inside compound native text is protected", \raw -> "(not " ++ raw ++ ")", \raw -> "(not " ++ raw ++ ")", \_ -> F.PAll [("x", F.boolSort)] (F.EVar "y"))
                , ("let body preserves free native alias", id, id, \_ -> F.ELet "x" F.PFalse (F.EVar "y"))
                , ("raw constant identifier is not captured", id, id, \_ -> F.PAll [("x", F.boolSort)] (F.ECon (F.L "_lq_bound_0" F.boolSort)))
                ]
            ]
        , testCase "trigger groups and body share alpha-freshening against a native alias" $ do
            let environment = mempty{F.seTheory = F.fromListSEnv [("y", F.Thy "y" "_lq_bound_0" F.boolSort F.Theory)]}
                quantified :: [[F.Symbol]] -> F.Symbol -> F.Triggered F.Expr
                quantified groups name = F.TR (F.Patterns [[F.EApp (F.EVar function) (F.EVar name) | function <- group] | group <- groups]) (F.PAll [(name, F.boolSort)] (F.PAnd [F.EVar "y", F.PIff (F.EApp (F.EVar "f") (F.EVar name)) (F.EVar name)]))
                fresh = F.intSymbol ("x" :: F.Symbol) (0 :: Int)
            mapM_
                ( \groups -> do
                    let rendered = lexicalRender environment (quantified groups "x")
                    rendered @?= lexicalRender environment (quantified groups fresh)
                    T.count ":pattern" (T.pack rendered) @?= length groups
                )
                [[["f"]], [["f"], ["g"]], [["f", "g"]]]
        , testCase "define-fun shares freshly chosen parameters with its body" $ do
            let raw = "_lq_bound_0"
                environment = mempty{F.seTheory = F.fromListSEnv [("y", F.Thy "y" (T.pack raw) F.boolSort F.Theory)]}
                definition = SMT.DefineFunc "identity" [("x", F.SBool)] F.SBool (F.PIff (F.EVar "x") (F.EVar "y"))
                script = "(set-logic ALL)\n(declare-fun " ++ raw ++ " () Bool)\n(assert " ++ raw ++ ")\n" ++ lexicalRender environment definition ++ "\n(assert (not (= (" ++ lexicalIdentifier "identity" ++ " false) false)))\n(check-sat)\n"
            result <- readProcess z3 ["-in"] script
            result @?= "unsat\n"
        , testGroup
            "actual SMT truth and false controls"
            [ testCase label $ do
                result <- readProcess z3 ["-in"] ("(set-logic ALL)\n(assert (not " ++ lexicalRender lexicalDecorated expression ++ "))\n(check-sat)\n")
                result @?= expected
            | (label, expression, expected) <-
                [ ("bound spelling cannot capture True", F.PAll [("x", F.boolSort)] F.PTrue, "unsat\n")
                , ("not every Boolean equals True", F.PAll [("x", F.boolSort)] (F.PIff (F.EVar "x") F.PTrue), "sat\n")
                , ("universal reflexivity", F.PAll [("x", F.intSort)] lexicalReflexive, "unsat\n")
                , ("universal is not constant zero", F.PAll [("x", F.intSort)] (lexicalEqual (F.EVar "x") (F.ECon (F.I 0))), "sat\n")
                , ("let keeps outer initializer", F.ELet "x" (F.EVar "x") (F.EVar "x"), "unsat\n")
                , ("let is not false", F.ELet "x" (F.EVar "x") (F.PNot (F.EVar "x")), "sat\n")
                , ("literal true binder cannot capture True", F.PAll [("true", F.boolSort)] F.PTrue, "unsat\n")
                , ("literal true binder is not always True", F.PAll [("true", F.boolSort)] (F.PIff (F.EVar "true") F.PTrue), "sat\n")
                , ("literal not binder cannot capture negation", F.PAll [("not", F.boolSort)] (F.POr [F.EVar "not", F.PNot (F.EVar "not")]), "unsat\n")
                , ("literal not binder is not its own negation", F.PAll [("not", F.boolSort)] (F.PIff (F.EVar "not") (F.PNot (F.EVar "not"))), "sat\n")
                , ("literal encoded alias remains a distinct binder", F.PAll [("true", F.boolSort), ("key$true", F.boolSort)] (F.PIff (F.EVar "true") (F.EVar "key$true")), "sat\n")
                , ("freshened actual retains the free reserved name", lexicalFreshenedReserved, "sat\n")
                ]
            ]
        ]

lexicalRender :: (SMT.SMTLIB2 a) => F.SymEnv -> a -> String
lexicalRender environment = B.unpack . toLazyByteString . fst . flip runState environment . SMT.smt2

lexicalIdentifier :: F.Symbol -> String
lexicalIdentifier = B.unpack . toLazyByteString . F.symbolBuilder

lexicalRenderScript :: F.SymEnv -> (F.SymEnv -> F.Expr) -> String
lexicalRenderScript environment expression = "(assert (not " ++ lexicalRender environment (expression environment) ++ "))"

lexicalDecorated :: F.SymEnv
lexicalDecorated =
    mempty
        { F.seSort = F.fromListSEnv [("x", F.boolSort)]
        , F.seTheory = F.fromListSEnv [("x", F.Thy "x" "true" F.boolSort F.Theory)]
        }

lexicalEqual :: F.Expr -> F.Expr -> F.Expr
lexicalEqual = F.PAtom F.Eq

lexicalReflexive :: F.Expr
lexicalReflexive = lexicalEqual (F.EVar "x") (F.EVar "x")

lexicalDefinition :: SMT.Command
lexicalDefinition = SMT.DefineFunc "identity" [("x", F.SInt)] F.SInt (F.EVar "x")

lexicalTriggered :: F.Triggered F.Expr
lexicalTriggered = F.TR (F.Patterns [[F.EApp (F.EVar "f") (F.EVar "x")]]) (F.PAll [("x", F.intSort)] (lexicalEqual (F.EApp (F.EVar "f") (F.EVar "x")) (F.EVar "x")))

lexicalFreshenedReserved :: F.Expr
lexicalFreshenedReserved =
    F.PAll [("true", F.boolSort), ("key$true", F.boolSort)] $
        F.subst1
            (F.PAll [("true", F.boolSort)] (F.PIff (F.EVar "input") (F.EVar "true")))
            ("input", F.EVar "true")

namesTests :: TestTree
namesTests =
    testGroup
        "reserved SMT identifiers"
        [ testCase "non-SMT symbol encoding is unchanged" $ do
            N.symbolSafeText "true" @?= "true"
            N.symbolSafeText "not" @?= "not"
            N.symbolText "true" @?= "true"
        , testCase "existing keyword escape is reused" $ do
            namesRendered "true" @?= "key$true"
            namesRendered "not" @?= "key$not"
            namesRendered "ordinary" @?= "key$ordinary"
            namesRendered "map" @?= "key$map"
        , testCase "encoded aliases and fresh suffixes remain distinct" $ do
            let roots = ["true", "false", "not", "and", "or", "ite", "forall", "select", "bvadd", "str.len"]
                names = nub $ concatMap namesVariants roots
                outputs = map namesRendered names
            length (nub outputs) @?= length names
            assertBool "reserved identifier remained raw" (all (\name -> namesRendered name /= N.symbolString name) roots)
        , testCase "prefixing does not inherit non-alpha aliases" $ do
            let names = ["", "fix$", "1", "fix$1", "key$", "key$true", "true", "\x03bb", "$955$", "key$955$", "a b", "a$32$b"]
            length (nub (map namesRendered names)) @?= length names
        , testCase "SMT bytes agree with the raw-text encoding" $
            mapM_ (\name -> namesRendered name @?= namesReference name) namesEncodingCases
        , testCase "symbol storage remains raw text" $
            mapM_
                ( \name -> do
                    Store.encode name @?= Store.encode (N.symbolText name)
                    case Store.decode (Store.encode name) of
                        Left problem -> assertBool (show problem) False
                        Right decoded -> do
                            decoded @?= name
                            namesRendered decoded @?= namesReference name
                )
                namesEncodingCases
        , testCase "repeated rendering shares the symbol encoding" $ do
            let name = N.symbol (T.replicate 1024 "a$\x03bb ")
                observations = [(index, name) | index <- [1 .. 128]]
                outputs = map renderNameObservation observations
            _ <- evaluate (force observations)
            bytes <- allocationBytes outputs
            mapM_ (\((index, _), output) -> B.unpack output @?= show index ++ namesReference name) (zip observations outputs)
            assertBool ("repeated SMT symbol encoding allocation: " ++ show bytes) (bytes < 16 * 1024 * 1024)
        ]

namesVariants :: N.Symbol -> [N.Symbol]
namesVariants name =
    name
        : N.symbol ("key$" <> N.symbolText name)
        : N.symbol ("key$36$" <> N.symbolText name)
        : [N.intSymbol root index | root <- [name, N.symbol ("key$" <> N.symbolText name)], index <- [0 :: Int .. 3]]

namesRendered :: N.Symbol -> String
namesRendered = B.unpack . toLazyByteString . N.symbolBuilder

namesEncodingCases :: [N.Symbol]
namesEncodingCases =
    concatMap namesVariants ["", "fix$", "1", "fix$1", "key$", "true", "map", "\x03bb", "$955$", "a b", "a$32$b"]
        ++ [N.symbol [character] | character <- ['\0' .. '\127'] ++ ['\x03bb', '\x1f600', '\x10ffff']]

namesReference :: N.Symbol -> String
namesReference name = "key$" ++ concatMap escape (N.symbolString name)
  where
    escape character
        | character `elem` (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ "_.") = [character]
        | otherwise = "$" ++ show (ord character) ++ "$"

-- Distinct observations keep the rendering call inside the measured traversal.
renderNameObservation :: (Int, N.Symbol) -> B.ByteString
renderNameObservation (index, name) = toLazyByteString (intDec index <> N.symbolBuilder name)
{-# NOINLINE renderNameObservation #-}

publicTests :: TestTree
publicTests =
    testGroup
        "public SMT name boundary"
        [ testCase label $
            bracket (SMT.makeContextNoLog Config.defConfig{Config.solver = Config.Z3}) SMT.cleanupContext $ \context -> do
                result <- evalStateT (SMT.checkValid' bindings F.PTrue expression) context
                result @?= expected
        | (label, bindings, expression, expected) <-
            [ ("reserved declaration excluded middle", [("not", F.boolSort)], F.POr [F.EVar "not", F.PNot (F.EVar "not")], True)
            , ("not every declared Boolean is True", [("not", F.boolSort)], F.EVar "not", False)
            , ("multiplication retains native preamble name", [], publicEqual (F.EBin F.Times (publicInteger 2) (publicInteger 3)) (publicInteger 6), True)
            , ("multiplication is not addition", [], publicEqual (F.EBin F.Times (publicInteger 2) (publicInteger 3)) (publicInteger 5), False)
            , ("division retains native preamble name", [], publicEqual (F.EBin F.Div (publicInteger 7) (publicInteger 3)) (publicInteger 2), True)
            , ("division is not multiplication", [], publicEqual (F.EBin F.Div (publicInteger 7) (publicInteger 3)) (publicInteger 21), False)
            ]
        ]

publicInteger :: Integer -> F.Expr
publicInteger = F.ECon . F.I

publicEqual :: F.Expr -> F.Expr -> F.Expr
publicEqual = F.PAtom F.Eq

modelTests :: TestTree
modelTests =
    testGroup
        "SMT response naming"
        [ testCase "ordinary escaped-looking names retain distinct source keys" $
            modelWithContext $ \context -> do
                let names = ["plain", "key$plain", "space name", "1", "fix$1"]
                    entries = zip names [7 .. 11]
                response <-
                    evalStateT
                        ( do
                            mapM_ (\(name, value) -> SMT.smtDecl name F.intSort >> SMT.smtAssert (F.PAtom F.Eq (F.EVar name) (F.ECon (F.I value)))) entries
                            _ <- SMT.command SMT.CheckSat
                            SMT.command (SMT.GetValue names)
                        )
                        context
                response @?= SMT.Values [(name, T.pack (show value)) | (name, value) <- entries]
        , testGroup
            "native aliases use request ownership"
            [ testCase label $ modelWithContext $ \context -> do
                response <-
                    evalStateT
                        ( do
                            SMT.smtFuncDecl raw ([], F.SInt)
                            modify (\current -> current{SMT.ctxSymEnv = mempty{F.seTheory = F.fromListSEnv [(name, F.Thy name raw F.intSort F.Theory) | name <- names]}})
                            SMT.smtAssert (F.PAtom F.Eq (F.EVar first) (F.ECon (F.I 17)))
                            _ <- SMT.command SMT.CheckSat
                            SMT.command (SMT.GetValue names)
                        )
                        context
                response @?= SMT.Values [(name, "17") | name <- names]
            | (label, raw, names@(first : _)) <-
                [ ("arbitrary wire spelling", "wire_elsewhere", ["original"])
                , ("encoded-looking native alias is not decoded globally", "key$plain", ["original"])
                , ("repeated aliased queries preserve multiplicity", "wire", ["first", "second", "first"])
                ]
            ]
        , testCase "unrequested response identifier is rejected explicitly" $ modelWithContext $ \context -> do
            let backend = Backend.Backend (const (pure "((unrequested 7))")) (const (pure ()))
            solver <- Backend.initSolver Backend.Queuing backend
            let fake = context{SMT.ctxSolver = solver}
            outcome <- try (evalStateT (SMT.command (SMT.GetValue ["plain"])) fake >>= evaluate . length . show) :: IO (Either SomeException Int)
            assertBool (show outcome) (either (isInfixOf "unrequested identifier" . show) (const False) outcome)
        , testCase "named unsat-core labels retain their independent spelling" $ do
            let name = B.unpack (toLazyByteString (F.symbolBuilder ("plain" :: F.Symbol)))
                render = B.unpack . toLazyByteString . fst . flip runState mempty . SMT.smt2
                script =
                    "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n(declare-fun "
                        ++ name
                        ++ " () Bool)\n"
                        ++ render (SMT.Assert (Just 7) (F.EVar "plain"))
                        ++ "\n"
                        ++ render (SMT.Assert (Just 8) (F.PNot (F.EVar "plain")))
                        ++ "\n(check-sat)\n(get-unsat-core)\n"
            response <- readProcess z3 ["-in"] script
            response @?= "unsat\n(p-7 p-8)\n"
        ]
modelWithContext :: (SMT.Context -> IO a) -> IO a
modelWithContext = bracket (SMT.makeContextNoLog Config.defConfig{Config.solver = Config.Z3}) SMT.cleanupContext

valuesTests :: TestTree
valuesTests =
    testGroup
        "retained elaborated child meanings"
        [ testCase label $ do
            let source = F.PAtom F.Eq expression (F.ECon (F.R expected))
                elaborated = Check.elabExpr valuesParameter Nothing source
                command = SMT.DefineFunc "addHalf" [("x", F.SReal)] F.SReal valuesHalfBody
                script =
                    "(set-logic ALL)\n"
                        ++ valuesRender command
                        ++ "\n(assert (not "
                        ++ valuesRender elaborated
                        ++ "))\n(check-sat)\n"
            result <- readProcess z3 ["-in"] script
            result @?= answer
        | (label, expression, expected, answer) <-
            [ ("integer argument retains real function value", once, 1.5, "unsat\n")
            , ("integer widening does not change the function value", once, 2.5, "sat\n")
            , ("nested annotated applications retain both function values", twice, 2.0, "unsat\n")
            , ("nested annotated applications retain countermodels", twice, 2.5, "sat\n")
            ]
        ]
  where
    once = F.ECst (F.EApp (F.EVar "addHalf") (F.ECon (F.I 1))) F.FReal
    twice = F.ECst (F.EApp (F.EVar "addHalf") once) F.FReal

valuesHalfBody :: F.Expr
valuesHalfBody = F.EBin F.Plus (F.EVar "x") (F.ECon (F.R 0.5))

valuesEnvironment :: F.SymEnv
valuesEnvironment =
    mempty
        { F.seSort = F.fromListSEnv [("addHalf", F.FFunc F.FReal F.FReal)]
        , F.seTheory = F.theorySymbols [F.Equ "addHalf" [("x", F.FReal)] valuesHalfBody F.FReal False]
        }

valuesParameter :: Check.ElabParam
valuesParameter = Check.ElabParam (Config.solverFlags Config.defConfig) "retained application values" valuesEnvironment

valuesRender :: (SMT.SMTLIB2 a) => a -> String
valuesRender value = B.unpack $ toLazyByteString $ evalState (SMT.smt2 value) valuesEnvironment

-- Use the solver supplied by the test environment, not a machine-specific path.
z3 :: FilePath
z3 = "z3"

-- Standalone entrypoints own a complete source judgment, unlike checkValid'.
-- A failed source judgment must be reported before solver simplification.
standaloneTests :: TestTree
standaloneTests =
    testGroup
        "standalone source preflight"
        [ testCase "ordinary declarations shadow native names" $ do
            valid <- SMT.checkValid cfg "" [("not", F.boolSort)] F.PTrue (F.POr [F.EVar "not", F.PNot (F.EVar "not")])
            valid @?= True
        , testCase "batch validity retains both truth and a countermodel" $ do
            valid <- SMT.checkValids cfg "" [("x", F.boolSort)] [F.POr [x, F.PNot x], x]
            valid @?= [True, False]
        , testCase "standalone source judgment includes native array functions" $ do
            let selected = F.EApp (F.EApp (F.EVar "select") (F.EVar "array")) one
            valid <- SMT.checkValid cfg "" [("array", F.arraySort F.intSort F.boolSort)] F.PTrue (F.PIff selected selected)
            valid @?= True
        , testCase "tautological disjunction cannot hide an invalid cast" $
            refused (SMT.checkValid cfg "" [] F.PTrue (F.POr [F.PTrue, malformed]))
        , testCase "false premise cannot hide an invalid conclusion" $
            refused (SMT.checkValid cfg "" [] F.PFalse malformed)
        , testCase "batch validates later predicates before returning results" $
            refused (SMT.checkValids cfg "" [] [F.PTrue, malformed])
        , testCase "one batch retains shared free-function equations" $ do
            let application value = F.EApp (F.EVar "function") value
            refused (SMT.checkValids cfg "" [("function", F.FVar 9)] [F.PAtom F.Eq (application one) one, F.PIff (application F.PTrue) F.PTrue])
        ]
  where
    cfg = Config.defConfig{Config.solver = Config.Z3, Config.save = False}
    x = F.EVar "x"
    one = F.ECon (F.I 1)
    malformed = F.ECst one F.boolSort
    refused action = do
        result <- try (action >> pure ()) :: IO (Either SomeException ())
        assertBool (show result) $ either (isInfixOf "SMT validity query" . show) (const False) result
