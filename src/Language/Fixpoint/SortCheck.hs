{-# LANGUAGE CPP                   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE InstanceSigs #-}
-- | This module has the functions that perform sort-checking, and related
-- operations on Fixpoint expressions and predicates.

module Language.Fixpoint.SortCheck  (
  -- * Sort Substitutions
    TVSubst
  , Env
  , mkSearchEnv
  , globalEnv
  , theoryEnv

  -- * Checking Well-Formedness
  , checkSorted
  , prepareSortCheck
  , SortCheckContext
  , extendSortCheck
  , checkSortAt
  , checkSortedReftFull
  , checkSortFull
  , pruneUnsortedReft

  -- * Sort inference
  , sortExpr
  , sortExprE
  , sortExprsWith
  , checkSortExpr
  , exprSort
  , exprSortMaybe

  -- * Unify
  , unifyFast
  , unifyFastWith
  , unifySorts
  , unifyTo1
  , unifyTo1With
  , sortFieldIndices
  , unifys

  -- * Apply Substitution
  , apply
  , defuncEApp

  -- * Exported Sorts
  , boolSort
  , strSort

  -- * Sort-Directed Transformations
  , ElabM
  , ElabParam (..)
  , Elaborate (..)
  , applySorts
  , elabApply
  , elabExpr
  , elabExprE
  , elabExprEAt
  , annotateExprEAt
  , instantiateEquationEAt
  , elaborateExpr
  , unApply
  , unElab
  , unElabSortedReft
  , unApplySortedReft
  , unApplyAt
  , toInt

  -- * Predicates on Sorts
  , isFirstOrder
  , isMono

--  , runCM0
  ) where

--  import           Control.DeepSeq
import Control.Monad
import Control.Monad.Except (catchError, throwError)
import Control.Monad.Reader
import Control.Monad.State.Strict (StateT, evalStateT, gets, modify')

import           Data.Bifunctor (first)
import qualified Data.Generics as Generics
import qualified Data.IntMap.Strict       as M
import qualified Data.HashSet              as S
import qualified Data.List                 as L
import           Data.Maybe                (mapMaybe, fromMaybe, isJust)
import qualified Data.HashMap.Strict       as HashMap
import qualified Data.Text                 as Text
import           Data.Tuple (swap)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Misc
import Language.Fixpoint.Types hiding (GInfo (..), senv)
import qualified Language.Fixpoint.Types.Config as Cfg
import qualified Language.Fixpoint.Types.Visitor  as Vis
import qualified Language.Fixpoint.Smt.Theories   as Thy
import           Text.PrettyPrint.HughesPJ.Compat
import           Text.Printf

import           GHC.Stack
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Types.Config (ElabFlags(elabExplicitKvars))

--import Debug.Trace as Debug

-- If set to 'True', enable precise logging via CallStacks.
debugLogs :: Bool
debugLogs = False

traced :: HasCallStack => (HasCallStack => String) -> String
traced str =
  if debugLogs
    then let prettified = prettyCallStack (popCallStack callStack)
         in str <> " (at " <> prettified <> ")"
    else str

--------------------------------------------------------------------------------
-- | Predicates on Sorts -------------------------------------------------------
--------------------------------------------------------------------------------
isMono :: Sort -> Bool
--------------------------------------------------------------------------------
isMono             = null . Vis.foldSort fv []
  where
    fv vs (FVar i) = i : vs
    fv vs _        = vs


--------------------------------------------------------------------------------
-- | Elaborate: make polymorphic instantiation explicit via casts,
--   make applications monomorphic for SMTLIB. This deals with
--   polymorphism by `elaborate`-ing all refinements except for
--   KVars. THIS IS NOW MANDATORY as sort-variables can be
--   instantiated to `int` and `bool`.
--------------------------------------------------------------------------------

type ElabM = Reader Cfg.ElabFlags

data ElabParam = ElabParam
  { epFlags :: Cfg.ElabFlags
  , epMsg   :: Located String
  , epEnv   :: SymEnv
  }

class Elaborate a where
  elaborate :: HasCallStack => ElabParam -> a -> a


instance (Loc a) => Elaborate (SInfo a) where
    elaborate ep si =
        si
            { F.cm = elaborate ep <$> F.cm si
            , F.bs = elaborate ep $ F.bs si
            , F.asserts = elaborate ep <$> F.asserts si
            , F.defns = elaborate ep $ F.defns si
            }


instance Elaborate (Triggered Expr) where
  elaborate ep (TR t e) = TR (elabTrigger t) (elaborate ep e)
    where
      -- explicit patterns mention the variables bound by the quantifier
      elabTrigger (Patterns ps) = Patterns (fmap (elaborate ep') <$> ps)
      ep'                       = ep { epEnv = insertsSymEnv (epEnv ep) (quantBinds e) }
      quantBinds (PAll   xts _) = xts
      quantBinds (PExist xts _) = xts
      quantBinds _              = []

instance (Elaborate a) => (Elaborate (Maybe a)) where
  elaborate ep t = elaborate ep <$> t

instance Elaborate Sort where
    -- Source constructors survive until serialization chooses their carrier.
    elaborate _ = id

instance Elaborate AxiomEnv where
  elaborate ep ae = ae
    { aenvEqs   = elaborate ep (aenvEqs ae)
    -- MISSING SORTS OOPS, aenvSimpl = elaborate msg env (aenvSimpl ae)
    }

instance Elaborate Rewrite where
    elaborate ep rw = rw{smBody = skipElabExpr ep' mempty (smBody rw)}
      where
        ep' = ep{epEnv = insertsSymEnv (epEnv ep) undefined}

instance Elaborate Equation where
    elaborate ep eq = eq{eqBody = skipElabExpr ep bindings (eqBody eq), eqArgs = arguments, eqSort = close (eqSort eq)}
      where
        close = resolveNumericSort (`lookupSEnv` seSort (epEnv ep))
        arguments = map (fmap close) (eqArgs eq)
        bindings = foldr (uncurry insertSEnv) mempty arguments

instance Elaborate DefinedFuns where
    elaborate ep (MkDefinedFuns eqs) = MkDefinedFuns (elabDefinedEqn ep <$> eqs)

elabDefinedEqn :: ElabParam -> Equation -> Equation
elabDefinedEqn ep eq =
    eq
        { eqBody = elaborateExpr (epFlags ep) (epEnv ep) (foldr (uncurry insertSEnv) mempty arguments) (epMsg ep) (eqBody eq) (Just t')
        , eqArgs = [(x, tx t) | (x, t) <- arguments]
        , eqSort = t'
        }
  where
    arguments = eqArgs eq
    tx = resolveNumericSort (`lookupSEnv` seSort (epEnv ep))
    t' = tx (eqSort eq)

instance Elaborate Expr where
    elaborate ~ep =
        let ~elaborateAt = elaborateExpr (epFlags ep) (epEnv ep) mempty
         in \e -> elaborateAt (epMsg ep) e Nothing

-- A diagnostic location varies independently of the immutable declarations.
-- Prepare those declarations once; each invocation still checks a fresh judgment.
-- The separate telescope binds terms, never declaration-owned type coordinates.
elaborateExpr :: (HasCallStack) => Cfg.ElabFlags -> SymEnv -> SEnv Sort -> Located String -> Expr -> Maybe Sort -> Expr
elaborateExpr ~ef ~env =
    \bindings ->
        let ~env' = env{seTheory = foldr deleteSEnv (seTheory env) (map fst (toListSEnv bindings))}
            ~elaborateAt = prepareAt bindings
         in \msg e t -> elabApply env' (either die id (elaborateAt msg t e))
  where
    ~prepareAt = elabExprEAt ef env

skipElabExpr :: ElabParam -> SEnv Sort -> Expr -> Expr
skipElabExpr ep bindings e = case elabExprEAt (epFlags ep) (epEnv ep) bindings (epMsg ep) Nothing e of
    Left _ -> e
    Right e' -> elabApply (epEnv ep){seTheory = foldr deleteSEnv (seTheory (epEnv ep)) (map fst (toListSEnv bindings))} e'

instance Elaborate (Symbol, Sort) where
  elaborate ep (x, s) = (x, elaborate ep s)

instance Elaborate a => Elaborate [a]  where
  elaborate ep xs = elaborate ep <$> xs

-- Integer multiplication/division use integer-only preamble functions.
-- Select the native real operation when either operand has a Real carrier.
-- Numeric class metadata alone does not change an SMT carrier.
numericOp :: SymEnv -> Bop -> Sort -> Sort -> Bop
numericOp env op left right
    | any ((== SReal) . sortSmtSort False env) [left, right] =
        case op of Times -> RTimes; Div -> RDiv; _ -> op
    | otherwise = op

instance Elaborate SortedReft where
    elaborate ~ep =
        let ~elaborateAt = elaborateSortedReft (epFlags ep) (epEnv ep)
         in \refinement -> elaborateAt (epMsg ep) refinement

-- The value declaration is local to each refinement, including both checks
-- against Bool. Only the immutable global preparation is shared across rows.
elaborateSortedReft :: (HasCallStack) => Cfg.ElabFlags -> SymEnv -> Located String -> SortedReft -> SortedReft
elaborateSortedReft ~ef ~env =
    \msg (RR source (Reft (value, predicate))) ->
        let s = resolveNumericSort (`lookupSEnv` seSort env) source
            body' = elaborateAt (fromListSEnv [(value, s)]) msg predicate (Just boolSort)
         in RR s (Reft (value, body'))
  where
    ~elaborateAt = elaborateExpr ef env

instance (Loc a) => Elaborate (BindEnv a) where
    elaborate ~ep =
        let ~elaborateAt = elaborateSortedReft (epFlags ep) (epEnv ep)
         in mapBindEnv (\i (x, sr, l) -> (x, elaborateAt (msg' l i x sr) sr, l))
      where
        msg' l i x sr = atLoc l (val (epMsg ep) ++ unwords [" elabBE", show i, show x, show sr])

instance (Loc a) => Elaborate (SimpC a) where
    elaborate ~ep =
        let ~elaborateAt = elaborateExpr (epFlags ep) (epEnv ep) mempty
         in \c -> c{_crhs = elaborateAt (atLoc c (val (epMsg ep))) (_crhs c) (Just boolSort)}



--------------------------------------------------------------------------------
-- | 'elabExpr' adds "casts" to decorate polymorphic instantiation sites.
--------------------------------------------------------------------------------
elabExpr :: (HasCallStack) => ElabParam -> Maybe Sort -> Expr -> Expr
elabExpr ~ep = runAt
  where
    ~elaborateAt = elabExprE ep
    runAt t e = case elaborateAt t e of
        Left ex -> die ex
        Right e' -> F.notracepp ("elabExp " ++ showpp e) e'

elabExprE :: ElabParam -> Maybe Sort -> Expr -> Either Error Expr
elabExprE ~ep =
    \t e -> elaborateAt msg t e
  where
    ~(ElabParam ef msg env) = ep
    ~elaborateAt = elabExprEAt ef env mempty

elabExprEAt :: Cfg.ElabFlags -> SymEnv -> SEnv Sort -> Located String -> Maybe Sort -> Expr -> Either Error Expr
elabExprEAt ~flags ~environment = expressionJudgmentEAt (\base terms -> inferExpected (Just base, terms)) flags (Just environment)

-- Source formation observes annotations before numeric coercion and native
-- application encoding. Native equality nevertheless has its actual configured
-- carrier meaning, including fresh polymorphic instance selection.
annotateExprEAt :: Cfg.ElabFlags -> Maybe SymEnv -> SEnv Sort -> Located String -> Maybe Sort -> Expr -> Either Error Expr
annotateExprEAt = expressionJudgmentEAt (\_ terms -> inferExpected (Nothing, terms))

-- An equation implicitly closes its original formal sort telescope. It does
-- not close arbitrary annotations discovered in the body or caller. First
-- form the selected owner call, then align the independently opened formal
-- telescope in that same judgment. This transports a body, not an axiom:
-- callers still select justified branches and check the resulting body.
instantiateEquationEAt :: Cfg.ElabFlags -> SymEnv -> SEnv Sort -> Located String -> Maybe Sort -> Equation -> Expr -> Either Error Expr
instantiateEquationEAt flags environment bindings location expected equation original =
    expressionJudgmentEAt instantiateBody flags (Just environment) bindings location expected original
  where
    instantiateBody native terms selected call = do
        let (headExpression, arguments) = splitEAppThroughECst call
        unless
            ( dropECst headExpression == EVar (eqName equation)
                && not (memberSEnv (eqName equation) bindings)
                && length arguments == length (eqArgs equation)
            )
            $ throwErrorAt "equation instantiation requires its selected, saturated declaration owner"
        reserveSorts [FVar index | index <- S.toList (sortFieldIndices equation)]
        intrinsicOwner <- checkSym terms (eqName equation)
        let retainOwner (EApp function argument) = EApp (retainOwner function) argument
            retainOwner (ECst expression annotation) = ECst (retainOwner expression) annotation
            retainOwner expression = ECst expression intrinsicOwner
        (typedCall, result) <- inferExpected (Just native, terms) selected (retainOwner call)
        formed <- readTVSubst
        let (_, actuals) = splitEAppThroughECst typedCall
            originalSorts = map snd (eqArgs equation) ++ [eqSort equation]
            names = S.toList (foldMap sortSymbols originalSorts)
            indices = S.toList (foldMap freeSortIndices originalSorts)
        symbolic <- forM names $ \name -> (\index -> (name, FVar index)) <$> fresh
        indexed <- forM indices $ \index -> (\freshIndex -> (index, FVar freshIndex)) <$> fresh
        let named = mkSortSubst symbolic
            numbered = M.fromList indexed
            open = substituteSort named numbered
        ownerSort <- resolveSort intrinsicOwner
        selectedSorts <- ownerTelescope (length actuals) ownerSort
        declarations <- asks chDeclarations
        _ <- unifys declarations (Just call) (map open originalSorts) selectedSorts
        solved <- readTVSubst
        inputs <- asks chInputIndices
        unless (all (\index -> apply formed (FVar index) == apply solved (FVar index)) (S.toList inputs)) $
            throwErrorAt "equation instantiation changed a formed caller coordinate"
        let transported =
                Vis.resolveExprSorts
                    (lookupNumericKind declarations)
                    numbered
                    (Vis.applyCoSub named (eqBody equation))
            values = mkSubst (zip (map fst (eqArgs equation)) actuals)
        pure (subst values transported, result)
    ownerTelescope 0 result = pure [result]
    ownerTelescope remaining (FFunc domain result) =
        (domain :) <$> ownerTelescope (remaining - 1) result
    ownerTelescope _ _ = throwErrorAt "equation instantiation lost its saturated owner telescope"

expressionJudgmentEAt :: (SymEnv -> Env -> Maybe Sort -> Expr -> CheckM (Expr, Sort)) -> Cfg.ElabFlags -> Maybe SymEnv -> SEnv Sort -> Located String -> Maybe Sort -> Expr -> Either Error Expr
expressionJudgmentEAt infer ~ef ~native = prepareAt
  where
    ~base = (fromMaybe mempty native){seSetBag = Cfg.elabSetBag ef}
    -- Only immutable declaration coordinates are shared. Expected sorts and
    -- expression fields still reserve their own coordinates in each judgment.
    ~baseIndices = sortFieldIndices (seSort base, seTheory base)
    ~declarations = (`lookupSEnvWithDistance` seSort base)
    prepareAt ~bindings = runAt
      where
        ~environmentIndices = baseIndices `S.union` sortFieldIndices bindings
        ~locals = resolveNumericSort (lookupNumericKind declarations) <$> bindings
        ~sEnv = locals <> seSort base
        ~envLookup = (`lookupSEnvWithDistance` sEnv)
        runAt msg t e =
            case runCM0 declarations (srcSpan msg) (Just ef) (environmentIndices `S.union` sortFieldIndices (t, e)) $ do
                -- Each occurrence has one inference judgment; annotations and
                -- its source sort are observations of that same judgment.
                (!e', _) <- infer base envLookup t e
                completeNativeEqualities (base <$ native)
                finalTheta <- readTVSubst
                return (applyExpr declarations finalTheta e') of
                Left (ChError f') ->
                    let e' = f' ()
                     in Left $ err (srcSpan e') (d (val e'))
                Right elab_e -> Right elab_e
          where
            d m =
                vcat
                    [ "elaborate" <+> text (val msg) <+> "failed on:"
                    , nest 4 (pprint e)
                    , "with error"
                    , nest 4 (text m)
                    , "in environment"
                    , nest 4 (pprint $ subEnv sEnv e)
                    ]

--------------------------------------------------------------------------------

-- Native equality constrains representations, not source constructors. Keep
-- judgment-created variables in that same translation until their carriers are
-- selected; erased source arguments cannot impose a representation constraint.
completeNativeEqualities :: Maybe SymEnv -> CheckM ()
completeNativeEqualities ~native = do
    obligations <- gets chNativeEqualities
    unless (null obligations) $ case native of
        Nothing -> validateSourceNativeEqualities
        Just base -> do
            selectNativeInstances base obligations
            finalTheta <- readTVSubst
            let numeric c = c == SInt || c == SReal
            forM_ obligations $ \(expression, left, right) -> do
                let carrier = sortSmtSort False base . apply finalTheta
                    c1 = carrier left
                    c2 = carrier right
                unless (c1 == c2 || (numeric c1 && numeric c2)) $
                    throwErrorAt (errRel expression (apply finalTheta left) (apply finalTheta right))

selectNativeInstances :: SymEnv -> [(Expr, Sort, Sort)] -> CheckM ()
selectNativeInstances environment obligations = loop
  where
    symbolic source = do
        inputs <- asks chInputIndices
        let variable i = if S.member i inputs then SInt else SVar i
        sortSmtSortWithVars variable environment <$> resolveSort source
    concrete source = sortSmtSort False environment <$> resolveSort source
    numeric sort = sort == SInt || sort == SReal
    aggregate SArray{} = True
    aggregate SSet{} = True
    aggregate SBag{} = True
    aggregate SData{} = True
    aggregate _ = False
    isAggregate (_, left, right) = do
        c1 <- symbolic left
        c2 <- symbolic right
        pure (aggregate c1 || aggregate c2)
    exact (expression, left, right) = do
        c1 <- symbolic left
        c2 <- symbolic right
        theta <- readTVSubst
        void (unifys emptySortEnv (Just expression) [representative c1] [representative c2])
            `withError` errRel expression (apply theta left) (apply theta right)
    scalar obligation@(_, left, right) = do
        c1 <- concrete left
        c2 <- concrete right
        unless (c1 == c2 || numeric c1 && numeric c2) (exact obligation)
    loop = do
        Th before <- readTVSubst
        classified <- forM obligations $ \obligation -> do
            aggregateRequirement <- isAggregate obligation
            pure (aggregateRequirement, obligation)
        let aggregates = [obligation | (True, obligation) <- classified]
            scalars = [obligation | (False, obligation) <- classified]
        mapM_ exact aggregates
        mapM_ scalar scalars
        Th after <- readTVSubst
        -- No coordinates are allocated here. Every changing round solves or
        -- aliases an existing fresh coordinate; occurs checking forbids cycles.
        unless (before == after) loop
    representative SInt = FInt
    representative SReal = FReal
    representative SBool = boolSort
    representative SString = strSort
    representative (SVar i) = FVar i
    representative (SArray index value) = arraySort (representative index) (representative value)
    representative (SSet element) = setSort (representative element)
    representative (SBag element) = bagSort (representative element)
    representative (SData constructor arguments) = L.foldl' FApp (FTC constructor) (map representative arguments)
    representative (SBitVec width) = sizedBitVecSort (symbol ("Size" ++ show width))
    representative (SFFld modulus) = finfieldSort (FNatNum modulus)

--------------------------------------------------------------------------------
-- | 'elabApply' replaces all direct function calls indirect calls via `apply`
--------------------------------------------------------------------------------
elabApply :: SymEnv -> Expr -> Expr
elabApply env = go
  where
    go e = case splitArgs e of
        (e', []) -> step e'
        (f, (argument, _) : rest)
            | ELam (name, _) body <- dropECst f ->
                go
                    ( L.foldl'
                        (\fun (arg, result) -> ECst (EApp fun arg) result)
                        (subst1 body (name, argument))
                        rest
                    )
        (f, es) -> defuncEApp env (go f) (first go <$> es)
    step (PAnd []) = PTrue
    step (POr []) = PFalse
    step (ENeg e) = ENeg (go e)
    step (EBin o e1 e2) = EBin o (go e1) (go e2)
    step (ELet x e1 e2)
        | Just sort <- exprSortMaybe e1
        , Just _ <- functionSort sort =
            go (subst1 e2 (x, e1))
        | otherwise = ELet x (go e1) (under [x] e2)
    step (EIte e1 e2 e3) = EIte (go e1) (go e2) (go e3)
    step (ECst e t) = ECst (go e) t
    step (PAnd ps) = PAnd (go <$> ps)
    step (POr ps) = POr (go <$> ps)
    step (PNot p) = PNot (go p)
    step (PImp p q) = PImp (go p) (go q)
    step (PIff p q) = PIff (go p) (go q)
    step (PExist bs p) = PExist bs (under (map fst bs) p)
    step (PAll bs p) = PAll bs (under (map fst bs) p)
    step (PAtom r e1 e2) = PAtom r (go e1) (go e2)
    step e@EApp{} = go e
    step (ELam b e) = ELam b (under [fst b] e)
    step (ECoerc a t e) = ECoerc a t (go e)
    step (PKVar k tsu su) = PKVar k tsu (mapKVarSubst go su)
    step e@ESym{} = e
    step e@ECon{} = e
    step e@EVar{} = e
    -- ETApp, ETAbs, PAll, PExist
    step e = error $ "TODO elabApply: " ++ showpp e
    under names = elabApply env{seTheory = foldr deleteSEnv (seTheory env) names}

--------------------------------------------------------------------------------
-- | Sort Inference ------------------------------------------------------------
--------------------------------------------------------------------------------
sortExpr :: Maybe SymEnv -> SrcSpan -> SEnv Sort -> Expr -> Sort
sortExpr ~native ~location ~environment =
    let ~inferAt = sortExprE native location environment mempty
     in \expression -> either die id (inferAt expression)

-- The fatal and optional interfaces observe the same inference judgment.
-- Declaration preparation is shared; equations and expression coordinates are not.
-- Lexical annotation sorts are interpreted in declarations before term insertion.
sortExprE :: Maybe SymEnv -> SrcSpan -> SEnv Sort -> SEnv Sort -> Expr -> Either Error Sort
sortExprE ~native ~location ~environment ~bindings = runAt
  where
    ~environmentIndices = nativeContextIndices native `S.union` sortFieldIndices (environment, bindings)
    ~declarations = (`lookupSEnvWithDistance` environment)
    ~locals = resolveNumericSort (lookupNumericKind declarations) <$> bindings
    ~terms = locals <> environment
    ~lookupAt = mkSearchEnv terms
    runAt e = case runCM0 declarations location Nothing (environmentIndices `S.union` sortFieldIndices e) (checkExpr lookupAt e <* completeNativeEqualities native >>= resolveSort) of
        Left (ChError failure) -> Left $ err location (diagnostic (val (failure ())))
        Right sort -> Right sort
      where
        diagnostic message =
            vcat
                [ "sortExpr failed on expression:"
                , nest 4 (pprint e)
                , "with error:"
                , nest 4 (text message)
                , "in environment"
                , nest 4 (pprint terms)
                ]

{- | Infer a jointly consumed batch in one fresh namespace. The caller reserves
coordinates in the judgment receiving these independently opened results.
-}
sortExprsWith :: Maybe SymEnv -> S.HashSet Int -> SrcSpan -> SEnv Sort -> SEnv Sort -> [Expr] -> [Sort]
sortExprsWith ~native ~occupied location environment bindings expressions =
    case runCM0
        declarations
        location
        Nothing
        (nativeContextIndices native `S.union` occupied `S.union` sortFieldIndices (environment, bindings, expressions))
        ((mapM (checkExpr (mkSearchEnv (locals <> environment))) expressions <* completeNativeEqualities native) >>= mapM resolveSort) of
        Left (ChError message) ->
            die $
                err location $
                    vcat
                        [ "sortExprsWith failed on expressions:"
                        , nest 4 (pprint expressions)
                        , "with error:"
                        , nest 4 (text (val (message ())))
                        , "in environment"
                        , nest 4 (pprint environment)
                        ]
        Right sorts -> sorts
  where
    declarations = mkSearchEnv environment
    locals = resolveNumericSort (lookupNumericKind declarations) <$> bindings

checkSortExpr :: Maybe SymEnv -> SrcSpan -> SEnv Sort -> Expr -> Maybe Sort
checkSortExpr ~native ~location ~environment =
    let ~inferAt = sortExprE native location environment mempty
     in \expression -> either (const Nothing) Just (inferAt expression)

nativeContextIndices :: Maybe SymEnv -> S.HashSet Int
nativeContextIndices = foldMap (\environment -> sortFieldIndices (seSort environment, seTheory environment))

subEnv :: (Subable e, Variable e ~ Symbol) => SEnv a -> e -> SEnv a
subEnv g e = intersectWithSEnv const g g'
  where
    g' = fromSetSEnv (syms e)


--------------------------------------------------------------------------------
-- | Checking Refinements ------------------------------------------------------
--------------------------------------------------------------------------------

-- | Types used throughout checker
type CheckM = ReaderT ChEnv (StateT ChState (Either ChError))

-- We guard errors with a lambda to prevent accidental eager
-- evaluation of the payload. This module is using -XStrict.
-- See also Note [Lazy error messages].
newtype ChError = ChError (() -> Located String)

instance Show ChError where
    show (ChError f) = show (f ())
data ChEnv = ChEnv
    { chInputIndices :: ~(S.HashSet Int)
    , chAliasPaths :: (S.HashSet Symbol, S.HashSet Symbol)
    , -- Lexical term extensions cannot reinterpret a declaration-owned FObj.
      chDeclarations :: Env
    , chSpan :: SrcSpan
    , chElabF :: Cfg.ElabFlags
    }

-- A judgment owns its solution, supply, and deferred carrier equations. Keep
-- their payloads lazy, as the former reference cells did, so an unused input
-- inventory is demanded only when the judgment allocates or classifies a sort.
data ChState = ChState
    { chCount :: ~(Int, S.HashSet Int)
    , chTVSubst :: ~TVSubst
    , chNativeEqualities :: ~[(Expr, Sort, Sort)]
    }

type Env = Symbol -> SESearch Sort
type ElabEnv = (Maybe SymEnv, Env)

--------------------------------------------------------------------------------
mkSearchEnv :: SEnv a -> Symbol -> SESearch a
--------------------------------------------------------------------------------
mkSearchEnv env x = lookupSEnvWithDistance x env

withError :: (HasCallStack) => CheckM a -> String -> CheckM a
act `withError` msg =
    act
        `catchError` ( \(ChError f) ->
                        throwError $ ChError $ \_ ->
                            let e = f ()
                             in atLoc e (val e ++ "\n  because\n" ++ msg)
                     )

-- Each judgment owns its supply. Demand complete input coordinates, including
-- unused forall labels, when allocating or distinguishing input variables.
runCM0 :: Env -> SrcSpan -> Maybe Cfg.ElabFlags -> S.HashSet Int -> CheckM a -> Either ChError a
runCM0 declarations sp mef ~occupied act =
    evalStateT
        (runReaderT act (ChEnv occupied (S.empty, S.empty) declarations sp (fromMaybe (Cfg.ElabFlags False False) mef)))
        (ChState (0, occupied) emptySubst [])

-- Without a complete native environment the source checker can rule out known
-- incompatible heads. This is its own admission judgment, not an extra condition
-- on configured elaboration's complete native-carrier judgment.
validateSourceNativeEqualities :: CheckM ()
validateSourceNativeEqualities = do
    equations <- gets chNativeEqualities
    forM_ equations $ \(expression, left, right) -> do
        left' <- resolveSort left
        right' <- resolveSort right
        unless ((left' == boolSort) == (right' == boolSort)) $
            throwErrorAt (errRel expression left' right')
        compatible <- compatibleAggregate left' right'
        unless compatible $
            throwErrorAt (errRel expression left' right')
  where
    -- Source-head checking rules out known incompatible representations even
    -- without a theory environment. Account for configured array lowering;
    -- configured elaboration checks the complete final SMT carriers below.
    compatibleAggregate left right = do
        let leftHead = aggregateHead left
            rightHead = aggregateHead right
        if leftHead == rightHead then pure True else lowerable leftHead rightHead

    aggregateHead sort = case unFApp (unAbs sort) of
        [FTC constructor, _] | symbol constructor `elem` [setConName, bagConName] -> Just (symbol constructor)
        [FTC constructor, _, _] | symbol constructor == arrayConName -> Just (symbol constructor)
        _ -> Nothing

    -- Lowering preserves Set's Boolean range and Bag's integer range, so
    -- they never become interchangeable. Either may compare to an explicitly
    -- array-typed operand; elaboration checks that Array's full carrier.
    lowerable (Just left) (Just right) = do
        ef <- asks chElabF
        pure $
            Cfg.elabSetBag ef
                && ( (left == arrayConName && right `elem` [setConName, bagConName])
                        || (right == arrayConName && left `elem` [setConName, bagConName])
                   )
    lowerable _ _ = pure False

sortFieldIndices :: (Generics.Data a) => a -> S.HashSet Int
sortFieldIndices = Generics.everythingBut S.union $
  Generics.mkQ (S.empty, False) sort
    `Generics.extQ` (atom :: Symbol -> (S.HashSet Int, Bool))
    `Generics.extQ` (atom :: Text.Text -> (S.HashSet Int, Bool))
    `Generics.extQ` (atom :: String -> (S.HashSet Int, Bool))
    `Generics.extQ` sortEnvironment
    `Generics.extQ` theoryEnvironment
 where
  sort :: Sort -> (S.HashSet Int, Bool)
  sort s = (sortIndices s, True)
  -- These typed folds enumerate every Sort field of the corresponding Data
  -- structures without rediscovering the map, key and record representation.
  sortEnvironment :: SEnv Sort -> (S.HashSet Int, Bool)
  sortEnvironment environment = (foldMap sortIndices environment, True)
  theoryEnvironment :: SEnv TheorySymbol -> (S.HashSet Int, Bool)
  theoryEnvironment environment = (foldMap (sortIndices . tsSort) environment, True)

  -- These closed representations contain no Sort, including virtual Data
  -- children. Keep generic traversal for every other field and constructor.
  atom :: a -> (S.HashSet Int, Bool)
  atom _ = (S.empty, True)

reserveSorts :: [Sort] -> CheckM ()
reserveSorts sorts = modify' $ \state ->
    let (next, occupied) = chCount state
     in state{chCount = (next, occupied `S.union` S.unions (map sortIndices sorts))}

fresh :: CheckM Int
fresh = do
    (next, occupied) <- gets chCount
    case available occupied next of
        Just n -> do
            modify' $ \state -> state{chCount = (if n == maxBound then n else n + 1, S.insert n occupied)}
            pure n
        Nothing -> throwErrorAt "sort-variable namespace exhausted"
  where
    available occupied n
        | not (S.member n occupied) = Just n
        | n == maxBound = Nothing
        | otherwise = available occupied (n + 1)

--------------------------------------------------------------------------------
-- | Checking Refinements ------------------------------------------------------
--------------------------------------------------------------------------------

checkSortedReftFull :: (Checkable a) => Maybe SymEnv -> SrcSpan -> SEnv SortedReft -> a -> ElabM (Maybe Doc)
checkSortedReftFull native sp γ = checkSorted native sp (sr_sort <$> γ)

checkSortFull :: (Checkable a) => Maybe SymEnv -> SrcSpan -> SEnv SortedReft -> Sort -> a -> ElabM (Maybe Doc)
checkSortFull native sp γ s t = do
    context <- prepareSortCheck native (sr_sort <$> γ)
    pure (checkSortAt context sp (Just s) t)

checkSorted :: (Checkable a) => Maybe SymEnv -> SrcSpan -> SEnv Sort -> a -> ElabM (Maybe Doc)
checkSorted native sp γ t = do
    context <- prepareSortCheck native γ
    pure (checkSortAt context sp Nothing t)

-- Local declarations shadow the immutable base. Lexical expression binders
-- extend term lookup only; type coordinates retain this declaration ownership.
data SortCheckContext
    = SortCheckContext
        ~(Maybe SymEnv)
        ~(SEnv Sort)
        ~(S.HashSet Int)
        ~Cfg.ElabFlags

prepareSortCheck :: Maybe SymEnv -> SEnv Sort -> ElabM SortCheckContext
prepareSortCheck ~native base = do
    ef <- ask
    pure (SortCheckContext native base (nativeContextIndices native `S.union` sortFieldIndices base) ef)

extendSortCheck :: SEnv Sort -> SortCheckContext -> SortCheckContext
extendSortCheck ~bindings ~(SortCheckContext native base occupied ef) =
    SortCheckContext native (bindings <> base) (occupied `S.union` sortFieldIndices bindings) ef

checkSortAt :: (Checkable a) => SortCheckContext -> SrcSpan -> Maybe Sort -> a -> Maybe Doc
checkSortAt ~(SortCheckContext native environment occupied ef) sp expected t =
    let ~declarations = (`lookupSEnvWithDistance` environment)
        ~indices = occupied `S.union` sortFieldIndices expected `S.union` sortFieldIndices t
        expression = checkingExpr expected t
        action = checkExprRaw declarations expression <* completeNativeEqualities native
     in case runCM0 declarations sp (Just ef) indices action of
            Left (ChError f) -> Just (text (val (f ())))
            Right _ -> Nothing

pruneUnsortedReft :: SEnv Sort -> Templates -> SortedReft -> SortedReft
pruneUnsortedReft _ t r
    | isEmptyTemplates t =
        r
pruneUnsortedReft γ t (RR source (Reft (value, predicate)))
    | isAnyTemplates t =
        -- this is the old code that checks everything
        RR s (Reft (value, close (tx filterAny predicate)))
    | otherwise =
        RR s (Reft (value, close (tx (filter filterWithTemplate) predicate)))
  where
    s = resolveNumericSort (`lookupSEnv` γ) source
    close = Vis.resolveExprSorts (`lookupSEnv` γ) mempty
    ~checkAt = checkPred' γ (value, s)
    filterAny = mapMaybe checkAt
    filterWithTemplate e = not (matchesTemplates t e) || isJust (checkAt e)
    tx f' = pAnd . f' . conjuncts

-- wmsg t r = "WARNING: prune unsorted reft:\n" ++ showFix r ++ "\n" ++ t

checkPred' :: SEnv Sort -> (Symbol, Sort) -> Expr -> Maybe Expr
checkPred' ~γ ~binding = \p ->
    case checkAt (ELam binding (PAnd [p])) of
        Left _err -> notracepp ("Removing" ++ showpp p) Nothing
        Right _ -> Just p
  where
    ~checkAt = sortExprE Nothing dummySpan γ mempty

-- Present each source judgment as an expression.
class (Generics.Data a) => Checkable a where
    checkingExpr :: Maybe Sort -> a -> Expr

instance Checkable Expr where
    checkingExpr expected expression = maybe expression (ECst expression) expected

instance Checkable SortedReft where
    -- A refinement's value uses the ordinary lexical-binder judgment.
    checkingExpr _ (RR source (Reft (value, predicate))) = ELam (value, source) predicate

--------------------------------------------------------------------------------

-- | Checking Expressions ------------------------------------------------------

--------------------------------------------------------------------------------
checkExpr                   :: Env -> Expr -> CheckM Sort
checkExpr environment expression = checkExprRaw environment expression >>= resolveSort

checkExprRaw :: Env -> Expr -> CheckM Sort
checkExprRaw f e = snd <$> elab (Nothing, f) e

addEnv :: (Eq a) => (a -> SESearch b) -> [(a, b)] -> a -> SESearch b
addEnv f bs x =
    case L.lookup x bs of
        Just s -> Found s
        Nothing -> f x

annotationSort :: Sort -> CheckM Sort
annotationSort s = do
    declarations <- asks chDeclarations
    return (resolveNumericSort (lookupNumericKind declarations) s)

--------------------------------------------------------------------------------
-- | Elaborate expressions with types to make polymorphic instantiation explicit.
--------------------------------------------------------------------------------
{-# SCC elab #-}
elab :: ElabEnv -> Expr -> CheckM (Expr, Sort)
elab environment expression = do
  (elaborated, sort) <- elabRaw environment expression
  solved <- resolveSort sort
  return (elaborated, solved)

elabRaw :: ElabEnv -> Expr -> CheckM (Expr, Sort)
--------------------------------------------------------------------------------
elabRaw f@(!environment, !_) e@(EBin !o !e1 !e2) = do
  (!e1', !s1) <- elab f e1
  (!e2', !s2) <- elab f e2
  !s <- checkOpTy e s1 s2
  forM_ environment $ \env -> do
    let carrier = sortSmtSort False env
        operation = numericOp env o s1 s2
        expected = if operation == RDiv || SReal `elem` [carrier s1, carrier s2] then SReal else SInt
    unless (all (`elem` [SInt, SReal]) [carrier s1, carrier s2] && carrier s == expected) $
      throwErrorAt (errOp e s1 s2)
  let operation = maybe o (\env -> numericOp env o s1 s2) environment
  let !result = EBin operation (eCst e1' s1) (eCst e2' s2)
  return (result, s)
elabRaw !f (EApp !e1 !e2) = do
    (e1', s1) <- elab f e1
    (e2', s2) <- elab f e2
    (!s1', !s2', !s) <- elabAppSort e1' e2' s1 s2
    let !e = eAppC s (eCst e1' s1') (eCst e2' s2')
    return (e, s)
elabRaw !_ e@(ESym _) =
  return (e, strSort)
elabRaw !_ e@(ECon (I _)) =
  return (e, FInt)
elabRaw !_ e@(ECon (R _)) =
  return (e, FReal)
elabRaw !_ e@(ECon (L _ s)) = do
  s' <- annotationSort s
  pure (e, s')

-- TODO: the guard below is because some LH tests generate PKVar with ill-sorted substitutions.
-- However, a cleaner solution could be to modify `Sanitize.restrictKVarDomain` to simply
-- those ill-sorted substitutions right up at the outset.
elabRaw !f e@(PKVar k tsu su) = do
  expKvars <- if isJust (fst f) then asks (elabExplicitKvars . chElabF) else pure False
  if expKvars
    then do
      xargs' <- forM (HashMap.toList $ fromKVarSubst su) $ \(x, arg) -> do
        (arg', _) <- elab f arg
        return (x, arg')
      return (PKVar k tsu (toKVarSubst (HashMap.fromList xargs')), boolSort)
    else
      return (e, boolSort)
elabRaw (!_, !f) e@(EVar !x) = do
  !cs <- checkSym f x
  -- Keep this occurrence's instantiation in the syntax for the final solution
  -- and encoding; looking the symbol up again would recover its declaration scheme.
  return (eCst e cs, cs)
elabRaw !f (ENeg !e) = do
  (!e', !s) <- elab f e
  declarations <- asks chDeclarations
  checkNumeric declarations s
  return (ENeg e', s)
elabRaw f (EIte !p !e1 !e2) = do
  p' <- elabPred f p
  (!e1', !s1) <- elab f e1
  (!e2', !s2) <- elab f e2
  !s <- checkIteTy p e1' e2' s1 s2
  return (EIte p' (eCst e1' s) (eCst e2' s), s)
elabRaw f (ELet !x !e1 !e2) = do
  (!e1', !t1) <- elab f e1
  (!e2', !t2) <- elab (elabAddEnv f [(x, t1)]) e2
  return (ELet x (eCst e1' t1) e2', t2)
elabRaw !f (ECst !e !t) = do
  t' <- annotationSort t
  (!e', !s) <- inferExpected f (Just t') e
  return (eCst e' s, s)
elabRaw !f (PNot !p) = do
  e' <- elabPred f p
  return (PNot e', boolSort)
elabRaw !f (PImp !p1 !p2) = do
  p1' <- elabPred f p1
  p2' <- elabPred f p2
  return (PImp p1' p2', boolSort)
elabRaw !f (PIff !p1 !p2) = do
  p1' <- elabPred f p1
  p2' <- elabPred f p2
  return (PIff p1' p2', boolSort)
elabRaw !f (PAnd !ps) = do
  ps' <- mapM (elabPred f) ps
  return (PAnd ps', boolSort)
elabRaw !f (POr !ps) = do
  ps' <- mapM (elabPred f) ps
  return (POr ps', boolSort)
elabRaw f e@(PAtom !eq !e1 !e2) | eq == Eq || eq == Ne = do
  (!e1', !t1) <- elab f e1
  (!e2', !t2) <- elab f e2
  (!t1', !t2') <- unite e t1 t2 `withError` errElabExpr e
  checkRelTy e eq t1 t2
  return (PAtom eq (eCst e1' t1') (eCst e2' t2'), boolSort)
elabRaw !f (PAtom !r !e1 !e2)
  | r == Ueq || r == Une = do
      (!e1', !s1) <- elab f e1
      (!e2', !s2) <- elab f e2
      checkURel (PAtom r e1 e2) s1 s2
      return (PAtom r e1' e2', boolSort)
elabRaw f@(!environment, !_) original@(PAtom !r !e1 !e2) = do
  first@(!e1', !s1) <- elab f e1
  second@(!e2', !s2) <- elab f e2
  checkRelTy original r s1 s2
  let operand pair = maybe (fst pair) (\env -> uncurry (toInt env) pair) environment
  return (PAtom r (operand first) (operand second), boolSort)
elabRaw !f (PExist !bs !e) = do
  bs' <- traverse (traverse annotationSort) bs
  e' <- elabPred (elabAddEnv f bs') e
  return (PExist bs' e', boolSort)
elabRaw !f (PAll !bs !e) = do
  bs' <- traverse (traverse annotationSort) bs
  e' <- elabPred (elabAddEnv f bs') e
  return (PAll bs' e', boolSort)
elabRaw !f (ELam (!x, !t) !e) = do
  t' <- annotationSort t
  (!e', !s) <- elab (elabAddEnv f [(x, t')]) e
  return (ELam (x, t') (eCst e' s), FFunc t' s)
elabRaw !f (ECoerc !s !t !e) = do
  s' <- annotationSort s
  t' <- annotationSort t
  (!e', !_) <- inferExpected f (Just s') e
  return (ECoerc s' t' e', t')
elabRaw !_ (ETApp _ _) =
  error "SortCheck.elab: TODO: implement ETApp"
elabRaw !_ (ETAbs _ _) =
  error "SortCheck.elab: TODO: implement ETAbs"

elabAddEnv :: ElabEnv -> [(Symbol, Sort)] -> ElabEnv
elabAddEnv (g, f) bs = (g, addEnv f bs)

elabPred :: ElabEnv -> Expr -> CheckM Expr
elabPred f e = do
  (e', s) <- elab f e
  checkBoolSort e s
  pure e'

inferExpected :: ElabEnv -> Maybe Sort -> Expr -> CheckM (Expr, Sort)
inferExpected f expected e = do
    (e', s) <- elab f e
    case expected of
        Nothing -> pure (e', s)
        Just t -> do
            t' <- annotationSort t
            theta <- assignSort (Just e) t' s `withError` errCast e s t'
            let target = apply theta t'
                -- A consumer may widen the scalar result, never the function's
                -- actual result annotation retained by ordinary application inference.
                result = case e of EApp{} -> eCst e' target; _ -> e'
            pure (result, target)

-- Source checking and elaboration constrain the same retained occurrences.
elabAppSort :: Expr -> Expr -> Sort -> Sort -> CheckM (Sort, Sort, Sort)
elabAppSort e1 e2 s1 s2 = do
    let e = Just (EApp e1 e2)
    (sIn, sOut) <- checkFunSort e s1
    solution <- assignSort e sIn s2
    pure (apply solution (FFunc sIn sOut), apply solution s2, apply solution sOut)


--------------------------------------------------------------------------------
-- | defuncEApp monomorphizes function applications.
--------------------------------------------------------------------------------
defuncEApp :: SymEnv -> Expr -> [(Expr, Sort)] -> Expr
defuncEApp _   e [] = e
defuncEApp env e ((function, _) : arguments)
    | EVar name <- dropECst e
    , Just declaration <- symEnvTheory name env
    , tsRaw declaration == ""
    , dropECst (fst (splitEAppThroughECst function)) /= EVar "_" =
        defuncEApp env function arguments
defuncEApp env e es = eCst (L.foldl' makeApplication e' es') (snd $ last es)
  where
    (e', es')       = takeArgs (seTheory env) e es

takeArgs :: SEnv TheorySymbol -> Expr -> [(Expr, a)] -> (Expr, [(Expr, a)])
takeArgs env e es =
    case Thy.isSmt2App env e of
        -- '_' constructs SMT indexed-identifier syntax, not a curried value.
        Just _ | dropECst e == EVar "_" -> (eApps e (fst <$> es), [])
        Just n
            | length es >= n ->
                let (es1, es2) = splitAt n es
                 in (eApps e (fst <$> es1), es2)
        _ -> (e, es)

-- 'e1' is the function, 'e2' is the argument, 's' is the OUTPUT TYPE
makeApplication :: Expr -> (Expr, Sort) -> Expr
makeApplication e1 (e2, s) =
  ECst (EApp (EApp f e1) e2) s
  where
    f  = {- notracepp ("makeApplication: " ++ showpp (e2, t2)) $ -} applyAt t2 s
    t2 = exprSort "makeAppl" e2

applyAt :: Sort -> Sort -> Expr
applyAt s t = ECst (EVar applyName) (FFunc s t)

-- JUST make "toInt" call "makeApplication" also, so they are wrapped in apply
-- MAY CAUSE CRASH (apply-on-apply) so rig `isSmt2App` to treat `apply` as SPECIAL.

-- TODO: proper toInt
toInt :: SymEnv -> Expr -> Sort -> Expr
toInt env e s
  | isSmtInt  = e
  | otherwise = ECst (EApp f (ECst e s)) FInt
  where
    isSmtInt  = isNum env s
    f         = toIntAt s

isNum :: SymEnv -> Sort -> Bool
isNum env s = case sortSmtSort False env s of
  SInt    -> True
  SString -> True
  SReal   -> True
  _       -> False


toIntAt :: Sort -> Expr
toIntAt s = ECst (EVar toIntName) (FFunc s FInt)

unElab :: Expr -> Expr
unElab = Vis.stripCasts . unApply

unElabSortedReft :: SortedReft -> SortedReft
unElabSortedReft sr = sr { sr_reft = mapPredReft unElab (sr_reft sr) }

unApplySortedReft :: SortedReft -> SortedReft
unApplySortedReft sr = sr { sr_reft = mapPredReft unApply (sr_reft sr) }

unApply :: Expr -> Expr
unApply = Vis.mapExprOnExpr go
  where
    go (ECst (EApp (EApp f e1) e2) _)
        | Just _ <- unApplyAt f = EApp e1 e2
    go e = e


unApplyAt :: Expr -> Maybe Sort
unApplyAt (ECst (EVar f) t@FFunc{})
  | f == applyName = Just t
unApplyAt _        = Nothing


splitArgs :: Expr -> (Expr, [(Expr, Sort)])
splitArgs = go []
  where
    go acc (ECst inner@(ECst _ source) target)
      | source == target = go acc inner
    go acc (ECst (EApp e1 e) s) = go ((e, s) : acc) e1
    go _   e@EApp{}             = errorstar $ "UNEXPECTED: splitArgs: EApp without output type: " ++ showpp e
    go acc e                    = (e, acc)

--------------------------------------------------------------------------------
{- | [NOTE:apply-monomorphization]

     Because SMTLIB does not support higher-order functions,
     all _non-theory_ function applications

        EApp e1 e2

     are represented, in SMTLIB, as

        (EApp (EApp apply e1) e2)

     where 'apply' is 'ECst (EVar "apply") t' and
           't'     is 'FFunc a b'
           'a','b' are the sorts of 'e2' and 'e1 e2' respectively.

     Note that *all polymorphism* goes through this machinery.

     Just before sending to the SMT solver, we use the cast 't'
     to generate a special 'apply_at_t' symbol.

     To let us do the above, we populate 'SymEnv' with the _set_
     of all sorts at which 'apply' is used, computed by 'applySorts'.
 -}

{- | [NOTE:coerce-apply] -- related to [NOTE:apply-monomorphism]

Haskell's GADTs cause a peculiar problem illustrated below:

```haskell
data Field a where
  FInt  :: Field Int
  FBool :: Field Bool

{-@ reflect proj @-}
proj :: Field a -> a -> a
proj fld x = case fld of
               FInt  -> 1 + x
               FBool -> not b
```

**The Problem**

The problem is you cannot encode the body of `proj` as a well-sorted refinement:

```haskell
    if is$FInt fld
        then (1 + (coerce (a ~ Int)  x))
        else (not (coerce (a ~ Bool) x))
```

The catch is that `x` is being used BOTH as `Int` and as `Bool`
which is not supported in SMTLIB.

**Approach: Uninterpreted Functions**

We encode `coerce` as an explicit **uninterpreted function**:

```haskell
    if is$FInt fld
        then (1 + (coerce@(a -> int)  x))
        else (not (coerce@(a -> bool) x))
```

where we define, extra constants in the style of `apply`

```haskell
   constant coerce@(a -> int ) :: a -> int
   constant coerce@(a -> bool) :: a -> int
```

However, it would not let us verify:


```haskell
{-@ reflect unwrap @-}
unwrap :: Field a -> a -> a
unwrap fld x = proj fld x

{-@ test :: _ -> TT @-}
test =  unwrap FInt  4    == 5
     && unwrap FBool True == False
```

because we'd get

```haskell
  unwrap FInt 4 :: { if is$FInt FInt then (1 + coerce_int_int 4) else ...  }
```

and the UIF nature of `coerce_int_int` renders the VC invalid.

**Solution: Eliminate Trivial Coercions**

HOWEVER, the solution here, may simply be to use UIFs when the
coercion is non-trivial (e.g. `a ~ int`) but to eschew them when
they are trivial. That is we would encode:

| Expr                   | SMTLIB             |
|:-----------------------|:-------------------|
| `coerce (a ~ int) x`   | `coerce_a_int x`   |
| `coerce (int ~ int) x` | `x`                |

which, I imagine is what happens _somewhere_ inside GHC too?

-}

--------------------------------------------------------------------------------
applySorts :: Vis.Foldable t => t -> [Sort]
--------------------------------------------------------------------------------
applySorts = {- tracepp "applySorts" . -} (defs ++) . Vis.fold vis () []
  where
    defs   = [FFunc t1 t2 | t1 <- basicSorts, t2 <- basicSorts]
    vis    = (Vis.defaultFolder :: Vis.Folder [KVar] t) { Vis.accExpr = go }
    go _ (EApp (ECst (EVar f) t) _)   -- get types needed for [NOTE:apply-monomorphism]
           | f == applyName
           = [t]
    go _ (ECoerc t1 t2 _)             -- get types needed for [NOTE:coerce-apply]
           = [FFunc t1 t2]
    go _ _ = []

--------------------------------------------------------------------------------
-- | Expressions sort  ---------------------------------------------------------
--------------------------------------------------------------------------------
exprSort :: String -> Expr -> Sort
exprSort msg e = fromMaybe (panic err') (exprSortMaybe e)
  where
    err'        = printf "exprSort [%s] on unexpected expression %s" msg (show e)

exprSortMaybe :: Expr -> Maybe Sort
exprSortMaybe expression =
    case runCM0 emptySortEnv dummySpan Nothing (sortFieldIndices expression) (judgment <* validateSourceNativeEqualities) of
        Left _ -> Nothing
        Right sort -> Just sort
  where
    judgment = go expression >>= resolveSort
    go (ECst _ s) = return s
    go (ELam (_, sx) e) = FFunc sx <$> go e
    go application@(EApp function argument) = do
        functionSort <- go function >>= resolveSort >>= instantiate
        case functionSort of
            FFunc domain result -> do
                argumentSort <- go argument
                solution <- assignSort (Just application) domain argumentSort
                return (apply solution result)
            _ -> throwErrorAt "exprSortMaybe: non-function application"
    go _ = throwErrorAt "exprSortMaybe: missing sort annotation"

unite :: Expr -> Sort -> Sort -> CheckM (Sort, Sort)
unite expression = withResolvedSorts (\declarations -> uniteResolved declarations expression)

uniteResolved :: Env -> Expr -> Sort -> Sort -> CheckM (Sort, Sort)
uniteResolved _ _ FInt FReal = return (FReal, FReal)
uniteResolved _ _ FReal FInt = return (FReal, FReal)
uniteResolved f e t1 t2 = do
    su <- unifys f (Just e) [t1] [t2]
    return (apply su t1, apply su t2)

throwErrorAt :: String -> CheckM a
throwErrorAt ~err' = do
    -- Lazy pattern needed because we use LANGUAGE Strict in this module
    -- See Note [Lazy error messages]
    sp <- asks chSpan
    throwError (ChError (\_ -> atLoc sp err'))

-- Note [Lazy error messages]
--
-- We don't want to construct error messages early, or
-- we might trigger some expensive computation of editDistance
-- when no error has actually occurred yet.

-- | Helper for checking symbol occurrences
checkSym :: Env -> Symbol -> CheckM Sort
checkSym f x = case f x of
    Found s -> instantiateWith (S.toList (S.filter (< 0) (freeSortIndices s))) s
    Alts xs -> throwErrorAt (errUnboundAlts x xs)

checkIteTy :: Expr -> Expr -> Expr -> Sort -> Sort -> CheckM Sort
checkIteTy p e1 e2 t1 t2 =
    (fst <$> unite e' t1 t2) `withError` errIte e1 e2 t1 t2
  where
    e' = EIte p e1 e2

checkOpTy :: Expr -> Sort -> Sort -> CheckM Sort
checkOpTy expression = withResolvedSorts (\declarations -> checkOpTyResolved declarations expression)

checkOpTyResolved :: Env -> Expr -> Sort -> Sort -> CheckM Sort
checkOpTyResolved f expression left right = do
    operand <- checkNumericTy f expression left right
    case expression of
        -- Native '/' returns Real even for two integer arguments.
        EBin RDiv _ _ -> return FReal
        -- SMT mod is integer-only; it is not source overloaded remainder.
        EBin Mod _ _ -> do
            when (numericKindAt f operand == FReal) (throwErrorAt (errOp expression left right))
            return operand
        _ -> return operand

checkNumericTy :: Env -> Expr -> Sort -> Sort -> CheckM Sort
checkNumericTy _ _ FInt FInt =
    return FInt
checkNumericTy _ _ FReal FReal =
    return FReal
-- Coercing int to real is somewhat suspicious, but z3 seems
-- to be ok with it
checkNumericTy _ _ FInt FReal =
    return FReal
checkNumericTy _ _ FReal FInt =
    return FReal
checkNumericTy f e t t' = do
    s <- unifys f (Just e) [t] [t'] `withError` errOp e t t'
    checkNumeric f (apply s t)
    return (apply s t)

checkFractional :: Env -> Sort -> CheckM ()
checkFractional f s@(FObj l)
  = do t <- checkSym f l
       unless (t `elem` [FFrac, realSort]) (throwErrorAt $ errNonFractional s)
checkFractional _ s
  = unless (isReal s) $ throwErrorAt (errNonFractional s)

checkNumeric :: Env -> Sort -> CheckM ()
checkNumeric f s@(FObj l)
  = do t <- checkSym f l
       unless (t `elem` [FNum, FFrac, intSort, FInt]) (throwErrorAt $ errNonNumeric s)
checkNumeric _ s
  = unless (isNumeric s) (throwErrorAt $ errNonNumeric s)

checkEqConstr :: Env -> Maybe Expr -> Symbol -> Sort -> CheckM ()
checkEqConstr _ _ a (FObj b)
    | a == b =
        return ()
checkEqConstr f e a t = do
    (path, opposite) <- asks chAliasPaths
    when (S.member a path) $
        throwErrorAt (errUnifyMsg (Just "cyclic declaration alias") e (FObj a) t)
    case f a of
        -- An opaque environment may reveal coordinates not present in the operands.
        -- Reserve the whole alias before descending, not each structural subtree.
        -- The path is local to this unfolding: acyclic sibling uses are independent.
        Found tA -> local (\context -> context{chAliasPaths = (S.insert a path, opposite)}) (reserveSorts [tA] >> unify1 f e tA t)
        _ -> throwErrorAt $ errUnifyMsg (Just "ceq2") e (FObj a) t

--------------------------------------------------------------------------------
-- | Checking Predicates -------------------------------------------------------
--------------------------------------------------------------------------------
checkBoolSort :: Expr -> Sort -> CheckM ()
checkBoolSort e s
  | s == boolSort = return ()
  | otherwise     = throwErrorAt (errBoolSort e s)

checkRelTy :: Expr -> Brel -> Sort -> Sort -> CheckM ()
checkRelTy expression relation = withResolvedSorts (\declarations -> checkRelTyResolved declarations expression relation)

checkRelTyResolved :: Env -> Expr -> Brel -> Sort -> Sort -> CheckM ()
checkRelTyResolved _ e Ueq s1 s2 = checkURel e s1 s2
checkRelTyResolved _ e Une s1 s2 = checkURel e s1 s2
checkRelTyResolved f _ _ s1@(FObj l) s2@(FObj l')
    | l /= l' =
        (checkNumeric f s1 >> checkNumeric f s2) `withError` errNonNumerics l l'
checkRelTyResolved _ _ _ FReal FReal = return ()
checkRelTyResolved _ _ _ FInt FReal = return ()
checkRelTyResolved _ _ _ FReal FInt = return ()
checkRelTyResolved f _ _ FInt s2 = checkNumeric f s2 `withError` errNonNumeric s2
checkRelTyResolved f _ _ s1 FInt = checkNumeric f s1 `withError` errNonNumeric s1
checkRelTyResolved f _ _ FReal s2 = checkFractional f s2 `withError` errNonFractional s2
checkRelTyResolved f _ _ s1 FReal = checkFractional f s1 `withError` errNonFractional s1
checkRelTyResolved f e Eq t1 t2 = void (unifys f (Just e) [t1] [t2] `withError` errRel e t1 t2)
checkRelTyResolved f e Ne t1 t2 = void (unifys f (Just e) [t1] [t2] `withError` errRel e t1 t2)
-- Ordering uses numeric capability, not nominal sort equality. Distinct
-- numeric constructors may compare without unifying their source types.
checkRelTyResolved _ e _ t1 t2 = unless (t1 == t2 || isNumeric t1 && isNumeric t2) (throwErrorAt $ errRel e t1 t2)

-- | @a ~~ b@ is translated to @(= a b)@ when producing SMTLIB.
-- But this is only valid if @a@ and @b@ have the same sort in SMTLIB.
-- It turns out that most types are represented with sort Int, so comparing
-- values of different types is not rejected in general by SMT solvers.
--
-- There are at least two exceptions though. The first of them is the type
-- Bool, which is represented with the sort Bool. Therefore, @a ~~ b@ is fine
-- if both arguments have Bool sort, or if neither of them has.
--
-- The other exception is functions, which have a function sort in SMTLIB.
-- But at the moment no @~~@ equalities are produced with function sorts, so
-- that case isn't considered in this function.
--
checkURel :: Expr -> Sort -> Sort -> CheckM ()
checkURel expression left right =
    -- Do not classify a free variable before the rest of its judgment has
    -- solved it. Every entrypoint checks Bool compatibility on completion;
    -- configured elaboration additionally checks the actual native carriers.
    modify' $ \state -> state{chNativeEqualities = (expression, left, right) : chNativeEqualities state}

--------------------------------------------------------------------------------

-- | Sort Unification

--------------------------------------------------------------------------------
unifyWith :: S.HashSet Int -> Env -> Maybe Expr -> Sort -> Sort -> Maybe TVSubst
unifyWith ~occupied f e t1 t2 =
    case runCM0 f dummySpan Nothing (occupied `S.union` sortFieldIndices (e, t1, t2)) ((unify1 f e t1 t2 >> readTVSubst) <* validateSourceNativeEqualities) of
        Left _ -> Nothing
        Right su -> Just su

--------------------------------------------------------------------------------
unifyTo1 :: Env -> [Sort] -> Maybe Sort
--------------------------------------------------------------------------------
unifyTo1 = unifyTo1With S.empty

unifyTo1With :: S.HashSet Int -> Env -> [Sort] -> Maybe Sort
unifyTo1With ~occupied f ts =
    case runCM0 f dummySpan Nothing (occupied `S.union` sortFieldIndices ts) (unifyTo1M f ts <* validateSourceNativeEqualities) of
        Left _ -> Nothing
        Right t -> Just t

--------------------------------------------------------------------------------
unifyTo1M :: Env -> [Sort] -> CheckM Sort
--------------------------------------------------------------------------------
unifyTo1M _ [] = panic "unifyTo1: empty list"
unifyTo1M f (t0 : ts) = foldM step t0 ts
  where
    step t t' = unify1 f Nothing t t' >> resolveSort t


--------------------------------------------------------------------------------
unifySorts :: Sort -> Sort -> Maybe TVSubst
--------------------------------------------------------------------------------
unifySorts = unifyFast False emptySortEnv

emptySortEnv :: Env
emptySortEnv _ = Alts []

--------------------------------------------------------------------------------

-- | Fast Unification; `unifyFast True` is just equality

--------------------------------------------------------------------------------
unifyFast :: Bool -> Env -> Sort -> Sort -> Maybe TVSubst
--------------------------------------------------------------------------------
unifyFast = unifyFastWith S.empty

{- | Reserve caller-owned coordinates outside the two operands, including any
environment aliases and later sorts to which the returned solution applies.
-}
unifyFastWith :: S.HashSet Int -> Bool -> Env -> Sort -> Sort -> Maybe TVSubst
unifyFastWith ~occupied False f t1 t2 = unifyWith occupied f Nothing t1 t2
unifyFastWith ~_ True _ t1 t2
    | t1 == t2 = Just emptySubst
    | otherwise = Nothing

{-
eqFast :: Sort -> Sort -> Bool
eqFast = go
  where
    go FAbs {} _       = False
    go (FFunc s1 s2) t = case t of
                          FFunc t1 t2 -> go s1 t1 && go s2 t2
                          _ -> False
    go (FApp s1 s2)  t = case t of
                          FApp t1 t2 ->  go s1 t1 && go s2 t2
                          _ -> False

    go (FTC s1) t      = case t of
                            FTC t1 -> s1 == t1
                            _ -> False

    go FInt FInt           = True
    go FReal FReal         = True
    go FNum FNum           = True
    go FFrac FFrac         = True
    go (FVar i1) (FVar i2) = i1 == i2
    go _ _                 = False

 -}
--------------------------------------------------------------------------------
unifys :: (HasCallStack) => Env -> Maybe Expr -> [Sort] -> [Sort] -> CheckM TVSubst
--------------------------------------------------------------------------------
-- Every equation extends the judgment's one solution. A failed equation rejects
-- the whole judgment; withError adds context but never retries a solved prefix.
unifys environment expression left right = do
    unifyMany environment expression left right
    readTVSubst

-- Equality of sorts and embedding an integer in a real-valued consumer are
-- distinct judgments. The embedding is scalar and directional; it does not
-- lift through arrays, function spaces, or arbitrary type constructors.
assignSort :: Maybe Expr -> Sort -> Sort -> CheckM TVSubst
assignSort expression expected actual = do
    environment <- asks chDeclarations
    initial <- readTVSubst
    case (numericKindAt environment (apply initial expected), numericKindAt environment (apply initial actual)) of
        (FReal, FInt) -> return initial
        (target, source) -> unifys environment expression [target] [source]

unifyMany :: (HasCallStack) => Env -> Maybe Expr -> [Sort] -> [Sort] -> CheckM ()
unifyMany f e ts ts'
    | length ts == length ts' =
        zipWithM_ (unify1 f e) ts ts'
    | otherwise = throwErrorAt (errUnifyMany ts ts')

unify1 :: Env -> Maybe Expr -> Sort -> Sort -> CheckM ()
unify1 f e left right = do
    theta <- readTVSubst
    unifyResolved f e theta (apply theta left) (apply theta right)

unifyResolved :: Env -> Maybe Expr -> TVSubst -> Sort -> Sort -> CheckM ()
unifyResolved environment expression theta left right
    | left' /= left || right' /= right =
        unifyResolved environment expression theta left' right'
  where
    left' = numericKindAt environment left
    right' = numericKindAt environment right
-- A resolved reflexive equation adds no information. In particular, opening
-- the same quantified scheme twice would manufacture unrelated fresh equations.
unifyResolved _ _ _ left right
    | left == right = return ()
unifyResolved _ e !θ (FVar !i) !t =
    unifyVar e θ i t
unifyResolved _ e !θ !t (FVar !i) =
    unifyVar e θ i t
unifyResolved f e _ (FApp !t1 !t2) (FApp !t1' !t2') =
    unifyMany f e [t1, t2] [t1', t2']
unifyResolved _ _ _ (FTC !l1) (FTC !l2)
    | isListTC l1 && isListTC l2 =
        return ()
unifyResolved f e _ t1@(FAbs _ _) !t2 = do
    !t1' <- instantiate t1
    unify1 f e t1' t2
unifyResolved f e _ !t1 t2@(FAbs _ _) = do
    !t2' <- instantiate t2
    unify1 f e t1 t2'
unifyResolved _ _ _ !s1 !s2
    | isString s1
    , isString s2 =
        return ()
unifyResolved f e _ !t FInt
    | t /= FReal =
        checkNumeric f t `withError` errUnify e t FInt
unifyResolved f e _ FInt !t
    | t /= FReal =
        checkNumeric f t `withError` errUnify e FInt t
unifyResolved f e _ !t FReal
    | t /= FInt =
        checkFractional f t `withError` errUnify e t FReal
unifyResolved f e _ FReal !t
    | t /= FInt =
        checkFractional f t `withError` errUnify e FReal t
unifyResolved f e _ (FFunc !t1 !t2) (FFunc !t1' !t2') =
    unifyMany f e [t1, t2] [t1', t2']
unifyResolved f e _ (FObj a) !t =
    checkEqConstr f e a t
unifyResolved f e _ !t (FObj a) =
    local (\context -> context{chAliasPaths = swap (chAliasPaths context)}) (checkEqConstr f e a t)
unifyResolved _ e _ !t1 !t2 =
    throwErrorAt (errUnify e t1 t2)

--------------------------------------------------------------------------------
instantiate :: Sort -> CheckM Sort
--------------------------------------------------------------------------------
instantiate = instantiateWith []

-- Implicit free negatives open first, then explicit binders inside-out.
-- Fresh images avoid every original coordinate, so all openings compose into
-- one substitution. Reversing the pairs keeps the innermost repeated binder.
instantiateWith :: [Int] -> Sort -> CheckM Sort
instantiateWith ~implicit t = do
    reserveSorts [t]
    let (bound, body) = bkAbs t
    pairs <- forM (implicit ++ reverse bound) $ \i -> do
        v <- fresh
        pure (i, FVar v)
    pure $ sortSubstVars (M.fromList (reverse pairs)) body

unifyVar :: Maybe Expr -> TVSubst -> Int -> Sort -> CheckM ()
unifyVar e θ i t
    | t == FVar i = return ()
    | FVar j <- t = do
        inputs <- asks chInputIndices
        -- A freshly opened forall may name an existing context coordinate, not
        -- rename that coordinate in the expression while leaving its context behind.
        updateTVSubst $
            if S.member i inputs && not (S.member j inputs)
                then updateVar j (FVar i) θ
                else updateVar i t θ
    | S.member i (freeSortIndices t) =
        throwErrorAt (errUnify e (FVar i) t ++ " (infinite free sort)")
    | otherwise = updateTVSubst (updateVar i t θ)

--------------------------------------------------------------------------------

-- | Update global subst to be applied to expressions

--------------------------------------------------------------------------------

readTVSubst :: CheckM TVSubst
readTVSubst = gets chTVSubst

updateTVSubst :: TVSubst -> CheckM ()
updateTVSubst theta = modify' $ \state -> state{chTVSubst = theta}

withResolvedSorts :: (Env -> Sort -> Sort -> CheckM a) -> Sort -> Sort -> CheckM a
withResolvedSorts classify left right = do
    environment <- asks chDeclarations
    left' <- resolveSort left
    right' <- resolveSort right
    classify environment (numericKindAt environment left') (numericKindAt environment right')

numericKindAt :: Env -> Sort -> Sort
numericKindAt environment = resolveNumericKind (lookupNumericKind environment)

lookupNumericKind :: Env -> Symbol -> Maybe Sort
lookupNumericKind environment name = case environment name of
    Found kind -> Just kind
    _ -> Nothing

resolveSort :: Sort -> CheckM Sort
resolveSort sort = (`apply` sort) <$> readTVSubst

--------------------------------------------------------------------------------

-- | Applying a Type Substitution ----------------------------------------------

--------------------------------------------------------------------------------
apply :: TVSubst -> Sort -> Sort
--------------------------------------------------------------------------------
apply (Th bindings) = sortSubstVars bindings

applyExpr :: Env -> TVSubst -> Expr -> Expr
applyExpr declarations (Th substitution) = Vis.resolveExprSorts (lookupNumericKind declarations) substitution

--------------------------------------------------------------------------------

-- | Deconstruct a function-sort -----------------------------------------------

--------------------------------------------------------------------------------
checkFunSort :: Maybe Expr -> Sort -> CheckM (Sort, Sort)
checkFunSort expression sort = resolveSort sort >>= checkFunSortResolved expression

checkFunSortResolved :: Maybe Expr -> Sort -> CheckM (Sort, Sort)
checkFunSortResolved expression t@FAbs{} = instantiate t >>= checkFunSort expression
checkFunSortResolved _ (FFunc t1 t2) = return (t1, t2)
checkFunSortResolved expression (FVar i) = do
    reserveSorts [FVar i]
    j <- fresh
    k <- fresh
    declarations <- asks chDeclarations
    _ <- unifys declarations expression [FVar i] [FFunc (FVar j) (FVar k)]
    return (FVar j, FVar k)
checkFunSortResolved _ t = throwErrorAt (errNonFunction 1 t)

--------------------------------------------------------------------------------

-- | API for manipulating Sort Substitutions -----------------------------------

--------------------------------------------------------------------------------

newtype TVSubst = Th (M.IntMap Sort) deriving (Show)

instance Semigroup TVSubst where
  (Th s1) <> (Th s2) = Th (s1 <> s2)

instance Monoid TVSubst where
  mempty  = Th mempty
  mappend = (<>)

updateVar :: Int -> Sort -> TVSubst -> TVSubst
updateVar !i !t (Th m) = Th (M.insert i t (M.map (sortSubstVars (M.singleton i t)) m))

emptySubst :: TVSubst
emptySubst = Th M.empty

--------------------------------------------------------------------------------
-- | Error messages ------------------------------------------------------------
--------------------------------------------------------------------------------

errElabExpr   :: Expr -> String
errElabExpr e = printf "Elaborate fails on %s" (showpp e)

errUnifyMsg :: Maybe String -> Maybe Expr -> Sort -> Sort -> String
errUnifyMsg msgMb eo t1 t2
  = printf "Cannot unify %s with %s %s %s"
      (showpp t1) {- (show t1) -} (showpp t2) {-(show t2)-} (errUnifyExpr eo) msgStr
    where
      msgStr = case msgMb of { Nothing -> ""; Just s -> "<< " ++ s ++ " >>"}

errUnify :: Maybe Expr -> Sort -> Sort -> String
errUnify = errUnifyMsg Nothing

errUnifyExpr :: Maybe Expr -> String
errUnifyExpr Nothing  = ""
errUnifyExpr (Just e) = "in expression: " ++ showpp e

errUnifyMany :: [Sort] -> [Sort] -> String
errUnifyMany ts ts'  = printf "Cannot unify types with different cardinalities %s and %s"
                         (showpp ts) (showpp ts')

errRel :: HasCallStack => Expr -> Sort -> Sort -> String
errRel e t1 t2       =
  traced $ printf "Invalid Relation %s with operand types %s and %s"
                         (showpp e) (showpp t1) (showpp t2)

errOp :: Expr -> Sort -> Sort -> String
errOp e t t'
  | t == t'          = printf "Operands have non-numeric types %s in %s"
                         (showpp t) (showpp e)
  | otherwise        = printf "Operands have different types %s and %s in %s"
                         (showpp t) (showpp t') (showpp e)

errIte :: Expr -> Expr -> Sort -> Sort -> String
errIte e1 e2 t1 t2   = printf "Mismatched branches in Ite: then %s : %s, else %s : %s"
                         (showpp e1) (showpp t1) (showpp e2) (showpp t2)

errCast :: Expr -> Sort -> Sort -> String
errCast e t' t       = printf "Cannot cast %s of sort %s to incompatible sort %s"
                         (showpp e) (showpp t') (showpp t)

errUnboundAlts :: Symbol -> [Symbol] -> String
errUnboundAlts x xs  = printf "Unbound symbol %s --- perhaps you meant: %s ?"
                         (showpp x) (L.intercalate ", " (showpp <$> xs))

errNonFunction :: Int -> Sort -> String
errNonFunction i t   = printf "The sort %s is not a function with at least %s arguments\n" (showpp t) (showpp i)

errNonNumeric :: Sort -> String
errNonNumeric  l     = printf "The sort %s is not numeric" (showpp l)

errNonNumerics :: Symbol -> Symbol -> String
errNonNumerics l l'  = printf "FObj sort %s and %s are different and not numeric" (showpp l) (showpp l')

errNonFractional :: Sort -> String
errNonFractional  l  = printf "The sort %s is not fractional" (showpp l)

errBoolSort :: Expr -> Sort -> String
errBoolSort     e s  = printf "Expressions %s should have bool sort, but has %s" (showpp e) (showpp s)

globalEnv :: Cfg.Config -> F.GInfo c a -> SEnv Sort
globalEnv cfg finfo = F.gLits finfo <> dataEnv
  where
    dataEnv = F.tsSort <$> theoryEnv cfg finfo

theoryEnv :: Cfg.Config -> F.GInfo c a -> F.SEnv F.TheorySymbol
theoryEnv cfg si
  =  Thy.theorySymbols (Cfg.solver cfg)
  <> Thy.theorySymbols (F.defns si)
  <> Thy.theorySymbols (F.ddecls si)
