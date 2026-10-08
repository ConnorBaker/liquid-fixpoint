-- | Validate and Transform Constraints to Ensure various Invariants -------------------------
--   1. Each binder must be associated with a UNIQUE sort
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Fixpoint.Solver.Sanitize
  ( -- * Transform FInfo to enforce invariants
    sanitize

    -- * Sorts for each Symbol (move elsewhere)
  , symbolEnv
  , shareFunctionLets

    -- * Remove substitutions K[x := e] where `x` is not in dom(K)
  , dropDeadSubsts
  ) where

import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Visitor
import           Language.Fixpoint.SortCheck     (theoryEnv, isFirstOrder)
-- import           Language.Fixpoint.Defunctionalize
import           Language.Fixpoint.Misc ((==>))
import qualified Language.Fixpoint.Misc                            as Misc
import qualified Language.Fixpoint.Types                           as F
import           Language.Fixpoint.Types.Config (Config)
import qualified Language.Fixpoint.Types.Config as Cfg
import qualified Language.Fixpoint.Types.Errors                    as E
import qualified Language.Fixpoint.Smt.Theories                    as Thy
import           Language.Fixpoint.Graph (kvEdges, CVertex (..))
import qualified Data.Bifunctor as Bifunctor (first)
import qualified Data.HashMap.Strict                               as M
import qualified Data.HashSet                                      as S
import qualified Data.List                                         as L
import qualified Data.Text                                         as T
import           Data.Maybe          (isNothing, mapMaybe, fromMaybe)
import           Control.Monad       ((>=>))
import qualified Control.Monad.State.Strict as St
import           GHC.Stack           (HasCallStack)
import           Text.PrettyPrint.HughesPJ hiding ((<>))
import qualified Language.Fixpoint.SortCheck as SortCheck

type SanitizeM a = Either E.Error a

-- Lift lexical, nonrecursive function lets into the existing defined-function
-- boundary before beta normalization. Their free terms become explicit typed
-- parameters; annotation ownership remains the original query declaration scope.
-- Unknown-dependent authored closures retain the ordinary interpretation path.
shareFunctionLets :: Config -> F.SInfo a -> F.SInfo a
shareFunctionLets cfg info = result{F.defns = F.defns info <> F.MkDefinedFuns (reverse definitions)}
  where
    (result, (_, _, definitions)) = St.runState transform (F.tempSymbol "lexical_definition" (0 :: Integer), occupied, [])
    original = symbolEnv cfg info
    declarations = F.seSort original
    fixed = S.fromList (map fst (F.toListSEnv (SortCheck.globalEnv cfg info <> F.dLits info)))
    expressions = [F.reftPred (F.sr_reft refinement) | (_, (_, refinement, _)) <- F.bindEnvToList (F.bs info)] ++ map F.crhs (M.elems (F.cm info)) ++ concatMap assertionExpressions (F.asserts info)
    assertionExpressions (F.TR (F.Patterns patterns) predicate) = predicate : concat patterns
    F.MkDefinedFuns existing = F.defns info
    occupied = S.fromList (map fst (F.toListSEnv declarations)) <> S.unions (map F.sortSymbols (map snd (F.toListSEnv declarations)) ++ map names expressions ++ map equationNames (existing ++ F.aenvEqs (F.ae info)))
    equationNames equation = S.fromList (F.eqName equation : map fst (F.eqArgs equation)) <> names (F.eqBody equation) <> S.unions (map F.sortSymbols (F.eqSort equation : map snd (F.eqArgs equation)))
    -- Global definition owners reserve free terms and free sort coordinates;
    -- scoped substitution protects unrelated nested lexical binders.
    names expression = F.syms expression <> exprFreeSortNames expression
    close = F.resolveNumericSort (`F.lookupSEnv` declarations)
    bind bindings locals = F.fromListSEnv [(name, (close sort, True)) | (name, sort) <- bindings] <> locals
    initial = F.fromListSEnv [(name, (close sort, True)) | (name, sort) <- F.toListSEnv declarations, not (S.member name fixed)]
    transform = do
        bindings <-
            traverse
                ( \(index, (name, refinement, annotation)) -> do
                    predicate <- walk (bind [(F.reftBind (F.sr_reft refinement), F.sr_sort refinement)] initial) (F.reftPred (F.sr_reft refinement))
                    pure (index, (name, refinement{F.sr_reft = F.Reft (F.reftBind (F.sr_reft refinement), predicate)}, annotation))
                )
                (F.bindEnvToList (F.bs info))
        constraints <-
            traverse
                ( \constraint -> do
                    predicate <- walk initial (F.crhs constraint)
                    pure constraint{F._crhs = predicate}
                )
                (F.cm info)
        assertions <- traverse (\(F.TR (F.Patterns patterns) predicate) -> F.TR <$> (F.Patterns <$> traverse (traverse (walk initial)) patterns) <*> walk initial predicate) (F.asserts info)
        pure info{F.bs = (F.bs info){F.beBinds = M.fromList bindings}, F.cm = constraints, F.asserts = assertions}
    walk locals (F.ELet name rhs body) = do
        rhs' <- walk locals rhs
        (previous, used, equations) <- St.get
        let defined = F.MkDefinedFuns (reverse equations)
            theory = Thy.theorySymbols defined <> F.seTheory original
            owned = (F.tsSort <$> theory) <> declarations
            environment = original{F.seTheory = theory, F.seSort = owned}
            (parameters, predicate) = lambdas rhs'
            generated = S.fromList (map F.eqName equations)
            globals = fixed `S.difference` S.fromList (map fst (F.toListSEnv locals))
            free = F.syms predicate `S.difference` S.fromList (map fst parameters) `S.difference` globals `S.difference` generated
            captures = [(variable, sort) | variable <- L.sort (S.toList free), Just (sort, _) <- [F.lookupSEnv variable locals]]
            safe = null (kvarsExpr rhs') && all (\variable -> maybe False snd (F.lookupSEnv variable locals)) (S.toList free)
        if not (null parameters) && safe && length captures == S.size free
            then do
                let checked = either E.die id (SortCheck.elabExprEAt (Cfg.solverFlags cfg) environment (fst <$> locals) "lexical definition" Nothing rhs')
                    (arguments, checkedBody) = lambdas checked
                    resultSort = SortCheck.exprSort "lexical definition result" checkedBody
                    (reserved, fresh) = F.freshInNS previous used
                    equation = F.mkEquation fresh (captures ++ arguments) checkedBody (close resultSort)
                    replacement = F.eApps (F.EVar fresh) [F.EVar variable | (variable, _) <- captures]
                St.put (fresh, reserved, equation : equations)
                walk locals (F.subst1 body (name, replacement))
            else do
                let sort = either (const Nothing) Just (SortCheck.sortExprE (Just environment) F.dummySpan owned (fst <$> locals) rhs')
                    independent = null (kvarsExpr rhs') && all (\variable -> maybe True snd (F.lookupSEnv variable locals)) (S.toList (F.syms rhs'))
                    inside = maybe (F.deleteSEnv name locals) (\value -> F.insertSEnv name (close value, independent) locals) sort
                F.ELet name rhs' <$> walk inside body
    walk locals (F.PAll bindings body) = F.PAll bindings <$> walk (bind bindings locals) body
    walk locals (F.PExist bindings body) = F.PExist bindings <$> walk (bind bindings locals) body
    walk locals (F.ELam binding body) = F.ELam binding <$> walk (bind [binding] locals) body
    walk locals expression = descend locals expression
    descend locals (F.EApp function argument) = F.EApp <$> walk locals function <*> walk locals argument
    descend locals (F.ENeg value) = F.ENeg <$> walk locals value
    descend locals (F.EBin operator left right) = F.EBin operator <$> walk locals left <*> walk locals right
    descend locals (F.EIte condition yes no) = F.EIte <$> walk locals condition <*> walk locals yes <*> walk locals no
    descend locals (F.ECst value sort) = (`F.ECst` sort) <$> walk locals value
    descend locals (F.PAnd values) = F.PAnd <$> traverse (walk locals) values
    descend locals (F.POr values) = F.POr <$> traverse (walk locals) values
    descend locals (F.PNot value) = F.PNot <$> walk locals value
    descend locals (F.PImp left right) = F.PImp <$> walk locals left <*> walk locals right
    descend locals (F.PIff left right) = F.PIff <$> walk locals left <*> walk locals right
    descend locals (F.PAtom relation left right) = F.PAtom relation <$> walk locals left <*> walk locals right
    descend locals (F.ECoerc source target value) = F.ECoerc source target <$> walk locals value
    -- Type abstraction cannot escape its lexical coordinate scope.
    descend _ value@F.ETAbs{} = pure value
    descend locals (F.ETApp value sort) = (`F.ETApp` sort) <$> walk locals value
    descend locals (F.PKVar variable types actuals) = do
        values <- traverse (walk locals) (F.fromKVarSubst actuals)
        pure (F.PKVar variable types (F.toKVarSubst values))
    descend _ value = pure value
    lambdas (F.ELam binding body) = let (bindings, predicate) = lambdas body in (binding : bindings, predicate)
    lambdas (F.ECst body _) | F.ELam{} <- F.dropECst body = lambdas body
    lambdas expression = ([], expression)

--------------------------------------------------------------------------------
sanitize :: (Show a) => Config -> F.SInfo a -> SanitizeM (F.SInfo a)
--------------------------------------------------------------------------------
sanitize cfg =
    banIrregularData
        >=> Misc.fM dropFuncSortedShadowedBinders
        >=> Misc.fM sanitizeWfC
        >=> Misc.fM replaceDeadKvars
        >=> Misc.fM (dropDeadSubsts . restrictKVarDomain cfg)
        >=> banMixedRhs
        >=> checkQualifiers cfg
        >=> banConstraintFreeVars cfg
        >=> Misc.fM addLiterals
        >=> Misc.fM (eliminateEta cfg)

--------------------------------------------------------------------------------
-- | 'dropAdtMeasures' removes all the measure definitions that correspond to
--   constructor, selector or test names for declared datatypes, as these are
--   now "natively" handled by the SMT solver.
--------------------------------------------------------------------------------
_dropAdtMeasures :: F.SInfo a -> F.SInfo a
_dropAdtMeasures si = si { F.ae = dropAdtAenv (F.ddecls si) (F.ae si) }

dropAdtAenv :: [F.DataDecl] -> F.AxiomEnv -> F.AxiomEnv
dropAdtAenv ds ae = ae { F.aenvSimpl = filter (not . isAdt) (F.aenvSimpl ae) }
  where
    isAdt         = (`S.member` adtSyms) . F.smName
    adtSyms       = adtSymbols ds

adtSymbols :: [F.DataDecl] -> S.HashSet F.Symbol
adtSymbols = S.fromList . map fst . concatMap Thy.dataDeclSymbols

--------------------------------------------------------------------------------
-- | `addLiterals` traverses the constraints to find (string) literals that
--   are then added to the `dLits` field.
--------------------------------------------------------------------------------
addLiterals :: F.SInfo a -> F.SInfo a
--------------------------------------------------------------------------------
addLiterals si = si { F.dLits = F.unionSEnv (F.dLits si) lits'
                    , F.gLits = F.unionSEnv (F.gLits si) lits'
                    }
  where
    lits'      = M.fromList [ (F.symbol x, F.strSort) | x <- symConsts si ]

--------------------------------------------------------------------------------
-- | `eliminateEta` converts equations of the form f x = g x into f = g
--------------------------------------------------------------------------------
eliminateEta :: Config -> F.SInfo a -> F.SInfo a
--------------------------------------------------------------------------------
eliminateEta cfg si
  | Cfg.etaElim cfg
  = si { F.ae = (ae {F.aenvEqs = etaElimNEW `fmap` F.aenvEqs ae }) }
  | otherwise
  = si
  where
    ae = F.ae si

    etaElimNEW eq = F.notracepp "Eliminating" $
                  let (f1, args1) = fapp (F.eqBody eq) in
                  let commonArgs = F.notracepp "commonArgs" .
                                           fmap fst .
                                           takeWhile (uncurry (==)) $
                                           zip args0 args1
                      commonLength = length commonArgs
                      (newArgsAndSorts, elimedArgsAndSorts) =
                                splitAt (length args - commonLength) argsAndSorts
                      args1' = F.eVar <$> reverse (drop commonLength args1) in
                  eq { F.eqArgs = newArgsAndSorts
                     , F.eqSort = foldr F.FFunc sort
                                       (snd <$> elimedArgsAndSorts)
                     , F.eqBody = F.eApps f1 args1'}
      where argsAndSorts = F.eqArgs eq
            args  = fst <$> argsAndSorts
            args0 = reverse args
            sort  = F.eqSort eq

    fapp :: F.Expr -> (F.Expr, [F.Symbol])
    fapp ee = fromMaybe (ee, []) (fapp' ee)

    fapp' :: F.Expr -> Maybe (F.Expr, [F.Symbol])
    fapp' (F.EApp e0 (F.EVar arg)) = do
      (fvar, args) <- fapp' e0
      splitApp (fvar, arg:args)
    fapp' e = pure (e, [])

    thySyms = theoryEnv cfg si

    splitApp (e, es)
      | isNothing $ F.notracepp ("isSmt2App? " ++ showpp e) $ Thy.isSmt2App thySyms (stripCasts e)
      = pure (e,es)
      | otherwise
      = Nothing


--------------------------------------------------------------------------------
-- | See issue liquid-fixpoint issue #230. This checks that whenever we have,
--      G1        |- K.su1
--      G2, K.su2 |- rhs
--   then
--      G1 \cap G2 \subseteq wenv(k)
--------------------------------------------------------------------------------
_banIllScopedKvars :: F.SInfo a ->  SanitizeM (F.SInfo a)
--------------------------------------------------------------------------------
_banIllScopedKvars si = Misc.applyNonNull (Right si) (Left . badKs) errs
  where
    errs              = concatMap (checkIllScope si kDs) ks
    kDs               = kvarDefUses si
    ks                = filter notKut $ M.keys (F.ws si)
    notKut            = not . (`F.ksMember` F.kuts si)

badKs :: [(F.KVar, F.SubcId, F.SubcId, F.IBindEnv)] -> F.Error
badKs = E.catErrors . map E.errIllScopedKVar

type KvConstrM = M.HashMap F.KVar [Integer]
type KvDefs    = (KvConstrM, KvConstrM)

checkIllScope :: F.SInfo a -> KvDefs -> F.KVar -> [(F.KVar, F.SubcId, F.SubcId, F.IBindEnv)]
checkIllScope si (inM, outM) k = mapMaybe (uncurry (isIllScope si k)) ios
  where
    ios                        = [(i, o) | i <- ins, o <- outs, i /= o ]
    ins                        = M.lookupDefault [] k inM
    outs                       = M.lookupDefault [] k outM

isIllScope :: F.SInfo a -> F.KVar -> F.SubcId -> F.SubcId -> Maybe (F.KVar, F.SubcId, F.SubcId, F.IBindEnv)
isIllScope si k inI outI
  | F.nullIBindEnv badXs = Nothing
  | otherwise            = Just (k, inI, outI, badXs)
  where
    badXs                = F.diffIBindEnv commonXs kXs
    kXs                  = {- F.tracepp ("kvarBinds " ++ show k) $ -} kvarBinds si k
    commonXs             = F.intersectionIBindEnv inXs outXs
    inXs                 = subcBinds si inI
    outXs                = subcBinds si outI

subcBinds :: F.SInfo a -> F.SubcId -> F.IBindEnv
subcBinds si i = F._cenv $ F.cm si M.! i

kvarBinds :: F.SInfo a -> F.KVar -> F.IBindEnv
kvarBinds si = F.wenv . (F.ws si M.!)

kvarDefUses :: F.SInfo a -> KvDefs
kvarDefUses si = (Misc.group ins, Misc.group outs)
  where
    es         = kvEdges si
    outs       = [(k, o) | (KVar k, Cstr o) <- es ]
    ins        = [(k, i) | (Cstr i, KVar k) <- es ]

--------------------------------------------------------------------------------
-- | `dropDeadSubsts` removes dead `K[x := e]` where `x` NOT in the domain of K.
--------------------------------------------------------------------------------
dropDeadSubsts :: F.SInfo a -> F.SInfo a
dropDeadSubsts si = mapKVarSubsts (\k su -> F.toKVarSubst $ M.filterWithKey (f k) $ F.fromKVarSubst su) si
  where
    kvsM          = M.mapWithKey (\k _ -> kvDom k) (F.ws si)
    kvDom         = S.fromList . F.kvarDomain si
    f k x _       = S.member x (M.lookupDefault mempty k kvsM)

--------------------------------------------------------------------------------
-- | `restrictKVarDomain` updates the kvar-domains in the wf constraints
--   to a subset of the original binders, where we DELETE the parameters
--   `x` which appear in substitutions of the form `K[x := y]` where `y`
--   is not in the env.
--------------------------------------------------------------------------------
restrictKVarDomain :: Config -> F.SInfo a -> F.SInfo a
restrictKVarDomain cfg si
  | Cfg.explicitKvars cfg = si
  | otherwise             = si { F.ws = M.mapWithKey (restrictWf kvm) (F.ws si) }
  where
    kvm                   = safeKvarEnv cfg si

-- | `restrictWf kve k w` restricts the env of `w` to the parameters in `kve k`.
restrictWf :: KvDom -> F.KVar -> F.WfC a -> F.WfC a
restrictWf kve k w = w { F.wenv = F.filterIBindEnv f (F.wenv w) }
  where
    f i            = S.member i kis
    kis            = S.fromList [ i | (_, i) <- F.toListSEnv kEnv ]
    kEnv           = M.lookupDefault mempty k kve

type KvDom     = M.HashMap F.KVar (F.SEnv F.BindId)
type KvBads    = M.HashMap F.KVar [F.Symbol]

-- | `safeKvarEnv` computes the "real" domain of each kvar, which is
--   a SUBSET of the input domain, in which we KILL the parameters
--   `x` which appear in substitutions of the form `K[x := y]`
--   where `y` is not in the env.

safeKvarEnv :: Config -> F.SInfo a -> KvDom
safeKvarEnv cfg si = L.foldl' (dropKvarEnv cfg si) env0 cs
 where
  cs = M.elems (F.cm si)
  env0 = initKvarEnv si

dropKvarEnv :: Config -> F.SInfo a -> KvDom -> F.SimpC a -> KvDom
dropKvarEnv cfg si kve c = M.mapWithKey (dropBadParams kBads) kve
 where
  kBads = badParams cfg si c

dropBadParams :: KvBads -> F.KVar -> F.SEnv F.BindId -> F.SEnv F.BindId
dropBadParams kBads k kEnv = L.foldl' (flip F.deleteSEnv) kEnv xs
 where
  xs = M.lookupDefault mempty k kBads

badParams :: Config -> F.SInfo a -> F.SimpC a -> M.HashMap F.KVar [F.Symbol]
badParams cfg si c = Misc.group bads
 where
  bads =
    [ (k, x)
    | (v, k, su) <- subcKSubs xsrs c
    , let vEnv = maybe sEnv (`S.insert` sEnv) v
    , (x, e) <- M.toList (F.fromKVarSubst su)
    , badArg vEnv e
    ]
  sEnv = S.fromList (map fst xsrs ++ map fst (F.toListSEnv (SortCheck.globalEnv cfg si)))
  xsrs = F.envCs (F.bs si) (F.senv c)

badArg :: S.HashSet F.Symbol -> F.Expr -> Bool
badArg sEnv e = not (F.syms e `S.isSubsetOf` sEnv)

type KSub = (Maybe F.Symbol, F.KVar, F.KVarSubst F.Symbol F.Symbol)

subcKSubs :: [(F.Symbol, F.SortedReft)] -> F.SimpC a -> [KSub]
subcKSubs xsrs c = rhs ++ lhs
 where
  lhs = concat [occurrences (Just v) p | (_, F.RR _ (F.Reft (v, p))) <- xsrs]
  rhs = occurrences Nothing (F.crhs c)
  occurrences v e = [(v, k, su) | (k, sus) <- M.toList (F.exprKVars e), su <- sus]


initKvarEnv :: F.SInfo a -> KvDom
initKvarEnv si = initEnv si <$> F.ws si

initEnv :: F.SInfo a -> F.WfC a -> F.SEnv F.BindId
initEnv si w = F.fromListSEnv [ (bind i, i) | i <- is ]
  where
    is       = F.elemsIBindEnv $ F.wenv w
    bind i   = Misc.fst3 (F.lookupBindEnv i be)
    be       = F.bs si

--------------------------------------------------------------------------------
-- | check that no constraint has free variables (ignores kvars)
--------------------------------------------------------------------------------
banConstraintFreeVars :: Config -> F.SInfo a -> SanitizeM (F.SInfo a)
banConstraintFreeVars cfg fi0 = Misc.applyNonNull (Right fi0) (Left . badCs) bads
  where
    fi      = mapKVars (const $ Just F.PTrue) fi0
    bads    = [(c, fs) | c <- M.elems $ F.cm fi, Just fs <- [cNoFreeVars fi k c]]
    k       = known cfg fi

known :: Config -> F.SInfo a -> F.Symbol -> Bool
known cfg fi  = \x -> F.memberSEnv x lits || F.memberSEnv x prims
  where
    lits  = F.gLits fi
    prims = theoryEnv cfg fi


cNoFreeVars :: F.SInfo a -> (F.Symbol -> Bool) -> F.SimpC a -> Maybe [F.Symbol]
cNoFreeVars fi knownSym c = if S.null fv then Nothing else Just (S.toList fv)
  where
    be   = F.bs fi
    ids  = F.elemsIBindEnv $ F.senv c
    cDom = [Misc.fst3 $ F.lookupBindEnv i be | i <- ids]
    cRng = S.unions $
      F.syms (F.crhs c) : [F.syms . F.sr_reft . Misc.snd3 $ F.lookupBindEnv i be | i <- ids]
    fv   = S.filter (not . knownSym) cRng `S.difference` S.fromList cDom

badCs :: Misc.ListNE (F.SimpC a, [F.Symbol]) -> E.Error
badCs = E.catErrors . map (E.errFreeVarInConstraint . Bifunctor.first F.subcId)

--------------------------------------------------------------------------------
-- | check that every DataDecl is regular
--------------------------------------------------------------------------------
banIrregularData :: F.SInfo a -> SanitizeM (F.SInfo a)
banIrregularData fi = Misc.applyNonNull (Right fi) (Left . badDataDecl) bads
  where
    bads = F.checkRegular (F.ddecls fi )

badDataDecl :: Misc.ListNE F.DataDecl -> E.Error
badDataDecl ds = E.catErrors [ E.errBadDataDecl d | d <- ds ]

--------------------------------------------------------------------------------
-- | Qualifiers are concrete predicates over their parameters and globals.
-- Unlike automatically mined candidates, malformed declarations are errors.
--------------------------------------------------------------------------------
checkQualifiers :: Config -> F.SInfo a -> SanitizeM (F.SInfo a)
--------------------------------------------------------------------------------
checkQualifiers cfg fi = Misc.applyNonNull (Right fi) (Left . E.catErrors) bads
 where
  bads =
    concat
      [ [ E.err (F.srcSpan q) (vcat ["Qualifier contains unknown predicates", pprint q, pprint ks])
        | let ks = M.keys (F.exprKVars (F.qBody q))
        , not (null ks)
        ]
          ++ [E.errFreeVarInQual q xs | let xs = free q, not (S.null xs)]
      | q <- F.quals fi
      ]
  free q = S.filter (not . isGlobal) (F.syms q)
  isGlobal x = F.memberSEnv x (SortCheck.globalEnv cfg fi)


--------------------------------------------------------------------------------
-- | check that each constraint has RHS of form [k1,...,kn] or [p]
--------------------------------------------------------------------------------
banMixedRhs :: F.SInfo a -> SanitizeM (F.SInfo a)
--------------------------------------------------------------------------------
banMixedRhs fi = Misc.applyNonNull (Right fi) (Left . badRhs) bads
  where
    ics        = M.toList $ F.cm fi
    bads       = [(i, c) | (i, c) <- ics, not $ isOk c]
    isOk c     = isKvarC c || isConcC c

badRhs :: Misc.ListNE (Integer, F.SimpC a) -> E.Error
badRhs = E.catErrors . map badRhs1

badRhs1 :: (Integer, F.SimpC a) -> E.Error
badRhs1 (i, c) = E.err E.dummySpan $ vcat [ "Malformed RHS for constraint id" <+> pprint i
                                          , nest 4 (pprint (F.crhs c)) ]

--------------------------------------------------------------------------------
-- | symbol |-> sort for EVERY variable in the SInfo; 'symbolEnv' can ONLY be
--   called with **sanitized** environments (post the uniqification etc.) or
--   else you get duplicate sorts and other such errors.
--------------------------------------------------------------------------------
symbolEnv :: HasCallStack => Config -> F.SInfo a -> F.SymEnv
symbolEnv cfg si = F.symEnv cfg sEnv thyEnv ds lits
  where
    thyEnv       = theoryEnv cfg si
    ds           = F.ddecls si
    sEnv         = (F.tsSort <$> thyEnv) `mappend` F.fromListSEnv xts
    xts          = symbolSorts cfg si ++ alits
    lits         = F.dLits si `F.unionSEnv'` F.fromListSEnv alits
    alits        = litsAEnv $ F.ae si

litsAEnv :: F.AxiomEnv -> [(F.Symbol, F.Sort)]
litsAEnv ae = zip (F.symbol <$> symConsts ae) (repeat F.strSort)

symbolSorts :: HasCallStack => Config -> F.GInfo c a -> [(F.Symbol, F.Sort)]
symbolSorts cfg fi = either E.die id $ symbolSorts' cfg fi

symbolSorts' :: Config -> F.GInfo c a -> SanitizeM [(F.Symbol, F.Sort)]
symbolSorts' _cfg fi  = (normalize . compact . (defs ++)) =<< bindSorts fi
  where
    normalize       = fmap (map (unShadow txFun dm))
    dm              = M.fromList defs
    defs            = F.toListSEnv . F.gLits $ fi
    txFun           = id

unShadow :: (F.Sort -> F.Sort) -> M.HashMap F.Symbol a -> (F.Symbol, F.Sort) -> (F.Symbol, F.Sort)
unShadow tx dm (x, t)
  | M.member x dm = (x, t)
  | otherwise     = (x, tx t)

_defuncSort :: F.Sort -> F.Sort
_defuncSort F.FFunc{} = F.funcSort
_defuncSort t         = t

compact :: [(F.Symbol, F.Sort)] -> Either E.Error [(F.Symbol, F.Sort)]
compact xts
  | null bad  = Right [(x, t) | (x, [t]) <- ok ]
  | otherwise = Left $ dupBindErrors bad'
  where
    bad'      = [(x, (, []) <$> ts) | (x, ts) <- bad]
    (bad, ok) = L.partition multiSorted . binds $ xts
    binds     = M.toList . M.map Misc.sortNub . Misc.group

--------------------------------------------------------------------------------
bindSorts  :: F.GInfo c a -> Either E.Error [(F.Symbol, F.Sort)]
--------------------------------------------------------------------------------
bindSorts fi
  | null bad   = Right [ (x, t) | (x, [(t, _)]) <- ok ]
  | otherwise  = Left $ dupBindErrors [ (x, ts) | (x, ts) <- bad]
  where
    (bad, ok)  = L.partition multiSorted . binds $ fi
    binds      = symBinds . F.bs


multiSorted :: (x, [t]) -> Bool
multiSorted = (1 <) . length . snd

dupBindErrors :: [(F.Symbol, [(F.Sort, [F.BindId] )])] -> E.Error
dupBindErrors = foldr1 E.catError . map dbe
  where
   dbe (x, y) = E.err E.dummySpan $ vcat [ "Multiple sorts for" <+> pprint x
                                         , nest 4 (pprint y) ]

--------------------------------------------------------------------------------
symBinds  :: F.BindEnv a -> [SymBinds]
--------------------------------------------------------------------------------
symBinds  = {- THIS KILLS ELEM: tracepp "symBinds" . -}
            M.toList
          . M.map Misc.groupList
          . Misc.group
          . binders

type SymBinds = (F.Symbol, [(F.Sort, [F.BindId])])

binders :: F.BindEnv a -> [(F.Symbol, (F.Sort, F.BindId))]
binders be = [(x, (F.sr_sort t, i)) | (i, (x, t, _)) <- F.bindEnvToList be]


--------------------------------------------------------------------------------
-- | Drop func-sorted `bind` that are shadowed by `constant` (if same type, else error)
--------------------------------------------------------------------------------
dropFuncSortedShadowedBinders :: F.SInfo a -> F.SInfo a
--------------------------------------------------------------------------------
dropFuncSortedShadowedBinders fi = dropBinders ok (const True) fi
  where
    ok x t  = M.member x defs ==> (F.allowHO fi || isFirstOrder t)
    defs    = M.fromList $ F.toListSEnv $ F.gLits fi

--------------------------------------------------------------------------------
-- | Drop irrelevant binders from WfC Environments
--------------------------------------------------------------------------------
sanitizeWfC :: F.SInfo a -> F.SInfo a
sanitizeWfC si = si { F.ws = ws' }
  where
    ws'        = deleteWfCBinds drops <$> F.ws si
    (_,drops)  = filterBindEnv keepF   $  F.bs si
    keepF      = conjKF [nonConstantF si, nonFunctionF si, _nonDerivedLH]

conjKF :: [KeepBindF] -> KeepBindF
conjKF fs x t = and [f x t | f <- fs]

-- | `nonDerivedLH` keeps a bind x if it does not start with `$` which is used
--   typically for names that are automatically "derived" by GHC (and which can)
--   blow up the environments thereby clogging instantiation, etc.
--   NOTE: This is an LH specific hack and should be moved there.

_nonDerivedLH :: KeepBindF
_nonDerivedLH x _ = not . T.isPrefixOf "$" . last . T.split ('.' ==) . F.symbolText $ x

nonConstantF :: F.SInfo a -> KeepBindF
nonConstantF si = \x _ -> not (x `F.memberSEnv` cEnv)
  where
    cEnv        = F.gLits si

nonFunctionF :: F.SInfo a -> KeepBindF
nonFunctionF si
  | F.allowHO si    = \_ _ -> True
  | otherwise       = \_ t -> isNothing (F.functionSort t)

--------------------------------------------------------------------------------
-- | Generic API for Deleting Binders from FInfo
--------------------------------------------------------------------------------
dropBinders :: KeepBindF -> KeepSortF -> F.SInfo a -> F.SInfo a
--------------------------------------------------------------------------------
dropBinders f g fi  = fi { F.bs    = bs'
                         , F.cm    = cm'
                         , F.ws    = ws'
                         , F.gLits = lits' }
  where
    -- discards        = diss
    (bs', discards) = filterBindEnv f $ F.bs fi
    cm'             = deleteSubCBinds discards   <$> F.cm fi
    ws'             = deleteWfCBinds  discards   <$> F.ws fi
    lits'           = F.filterSEnv g (F.gLits fi)

type KeepBindF = F.Symbol -> F.Sort -> Bool
type KeepSortF = F.Sort -> Bool

deleteSubCBinds :: [F.BindId] -> F.SimpC a -> F.SimpC a
deleteSubCBinds bs sc = sc { F._cenv = foldr F.deleteIBindEnv (F.senv sc) bs }

deleteWfCBinds :: [F.BindId] -> F.WfC a -> F.WfC a
deleteWfCBinds bs wf = wf { F.wenv = foldr F.deleteIBindEnv (F.wenv wf) bs }

filterBindEnv :: KeepBindF -> F.BindEnv a -> (F.BindEnv a, [F.BindId])
filterBindEnv f be  = (keepBindEnv , discard')
  where
    keepBindEnv     = F.bindEnvFromList [(i, (x, sr, a)) | (i, (x, sr, a)) <- keep]
    (keep, discard) = L.partition f' $ F.bindEnvToList be
    discard'        = fst <$> discard
    f' (_, (x, t, _)) = f x (F.sr_sort t)


---------------------------------------------------------------------------
-- | Replace KVars that do not have a WfC with PFalse
---------------------------------------------------------------------------
replaceDeadKvars :: F.SInfo a -> F.SInfo a
---------------------------------------------------------------------------
replaceDeadKvars fi = mapKVars go fi
  where
    go k | k `M.member` F.ws fi = Nothing
         | otherwise            = Just F.PFalse
