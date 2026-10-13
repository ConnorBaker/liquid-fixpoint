{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wwarn #-}

module Language.Fixpoint.Solver.Solution
  ( -- * Create Initial Solution
    init

    -- * Update Solution
  , Sol.update

    -- * Apply Solution
  , applyInSortedReft
  , CombinedEnv
  , combinedEnv
  , qbPreds
  , applyExpr

    -- * Lookup Solution
  , lhsPred
  , SummaryState
  , prepareSummaryState
  , lhsPredShared

  , nonCutsResult

    -- * Save Solution
  , saveSolution

    -- * Exported for Testing
  , simplifyKVar
  , alphaEq
  ) where

import           Control.Arrow (second)
import           Control.Monad                  (guard, mplus, when)
import           Data.Functor.Identity (Identity(..))
import qualified Data.Generics as Generics
import           Control.Monad.Reader
import qualified Control.Monad.State.Strict as St
import qualified Data.Map.Strict as Ordered
import qualified Data.HashSet                   as S
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as List
import           Data.Maybe                     (maybeToList, isJust, isNothing)
import qualified Data.Text as Text
import qualified Text.PrettyPrint.HughesPJ      as PJ
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Types.Visitor      as V
import           Language.Fixpoint.SortCheck          (ElabM)
import qualified Language.Fixpoint.SortCheck          as So
import           Language.Fixpoint.Solver.Sanitize    (symbolEnv)
import qualified Language.Fixpoint.Smt.Theories       as Thy
import           Language.Fixpoint.Misc               (ensurePath)
import qualified Language.Fixpoint.Misc               as Misc
import qualified Language.Fixpoint.Utils.Files        as Files
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types              as F
import qualified Language.Fixpoint.Types.Solutions    as Sol
import           Language.Fixpoint.Types.Constraints  hiding (ws, bs)
import           Prelude                              hiding (init, lookup)


--------------------------------------------------------------------------------
-- | Initial Solution (from Qualifiers and WF constraints) ---------------------
--------------------------------------------------------------------------------
init :: (F.Fixpoint a) => Config -> F.SInfo a -> S.HashSet F.KVar -> M.HashMap F.KVar Sol.QBind
--------------------------------------------------------------------------------
init cfg si ks =
    runReader initialize (solverFlags cfg)
  where
    initialize = do
        context <- So.prepareSortCheck (Just native) mempty
        traverse (refine context si qcs genv) ws
    native = symbolEnv cfg si
    qcs = mkQCluster (F.quals si)
    ws = M.intersection (F.ws si) (S.toMap ks)
    genv = initQualifierEnv cfg si

initQualifierEnv :: (F.Fixpoint a) => Config -> F.SInfo a -> F.SEnv F.Sort
initQualifierEnv cfg si
  | scraping  = So.globalEnv cfg si <> instConstants si
  | otherwise = instConstants si
  where
    scraping = scrape cfg /= No

--------------------------------------------------------------------------------
-- | [NOTE:qual-cluster] It is wasteful to perform instantiation *individually*
--   on each qualifier, as many qualifiers have "equivalent" parameters, and
--   so have the "same" instances in an environment. To exploit this structure,
--
--   1. Group the [Qualifier] into a QCluster
--   2. Refactor instK to use QCluster
--------------------------------------------------------------------------------

type QCluster = M.HashMap QCSig [Qualifier]

type QCSig = [F.QualParam]

mkQCluster :: [Qualifier] -> QCluster
mkQCluster = Misc.groupMap qualSig

qualSig :: Qualifier -> QCSig
qualSig q = [ p { F.qpSym = F.dummyName }  | p <- F.qParams q ]

--------------------------------------------------------------------------------

refine :: So.SortCheckContext -> F.SInfo a -> QCluster -> F.SEnv F.Sort -> F.WfC a -> ElabM Sol.QBind
refine context info qs genv w = refineK (env `seq` So.extendSortCheck env context) (allowHOquals info) env lits qs (F.wvvs w)
  where
    env = wenvSort <> genv
    wenvSort = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs info) (F.wenv w))
    lits = getConstants info

instConstants :: F.SInfo a -> F.SEnv F.Sort
instConstants = F.fromListSEnv . filter notLit . F.toListSEnv . F.gLits
  where
    notLit = not . F.isLitSymbol . fst

refineK :: So.SortCheckContext -> Bool -> F.SEnv F.Sort -> [F.Constant] -> QCluster -> [(F.Symbol, F.Sort)] -> ElabM Sol.QBind
refineK context ho env lits qs vvs =
    Sol.qbFilterM (pure . okInst (So.checkSortAt context) vvs) eqs
  where
    eqs = instK ho env lits vvs qs

--------------------------------------------------------------------------------
-- | @instK ho env lits vvs qc@ instantiates the qualifiers in @qc@ for a kvar
--   with value variables @vvs@. The first (non-literal) parameter of each
--   qualifier is instantiated with a value variable, and the rest with any
--   other symbol in @env@, which includes the value variables. A kvar without
--   value variables only gets @false@ as a candidate.
instK :: Bool
      -> F.SEnv F.Sort
      -> [F.Constant]
      -> [(F.Symbol, F.Sort)]
      -> QCluster
      -> Sol.QBind
--------------------------------------------------------------------------------
instK _  _   _    []  _  = Sol.qb [Sol.falseEqual]
instK ho env lits vvs qc = Sol.qb . unique $
  [ Sol.eQual q xs ls
      | (sig, qs) <- M.toList qc
      , let (varSig, litSig) =  splitSig sig
      , xs        <- instKSig ho env vvs varSig
      , ls        <- instLitSig lits litSig
      , q         <- qs
  ]

-- split the QCSig into the parts that are for regular variables vs for wildcard-literals that are defined as `a#`, `b#` etc.
-- e.g. see tests/horn/pos/wild_lits*.smt2
splitSig :: QCSig -> (QCSig, QCSig)
splitSig = List.partition (\qp -> qpPat qp /= PatLit)

instLitSig :: [F.Constant] -> QCSig -> [[F.Constant]]
instLitSig lits sig = sequence [ filter (matchSort (qpSort qp)) lits | qp <- sig ]

matchSort :: F.Sort -> F.Constant -> Bool
matchSort F.FInt  (F.I _)    = True
matchSort F.FReal (F.R _)    = True
matchSort s       (F.L _ s') = s == s'
matchSort _       _          = False

unique :: [Sol.EQual] -> [Sol.EQual]
unique qs = M.elems $ M.fromList [ (Sol.eqPred q, q) | q <- qs ]

-- | @instKSig ho env vvs sig@ instantiates the first parameter of @sig@ with a
--   value variable in @vvs@, and the remaining parameters with symbols in @env@
--   and value variables other than the one chosen for the first parameter. The
--   name pattern of the first parameter is ignored.
instKSig :: Bool
         -> F.SEnv F.Sort
         -> [(F.Symbol, F.Sort)]
         -> QCSig
         -> [[F.Symbol]]
instKSig _  _   _   [] = error "Empty qsig in Solution.instKSig"
instKSig ho env vvs (qp:qps) = do
  ixs    <- matchP occupied symToSrch (vvQP : restQPs)
  x : ys <- instSymbol (vvTyss ++ tyss) (reverse ixs)
  guard (x `notElem` ys)
  return (x : ys)
  where
    vvQP       = (vvTyss, qp { F.qpPat = F.PatNone })
    restQPs    = [ (tyss, qp') | qp' <- qps ]
    -- value variables use negative indices to keep them apart from the env
    vvTyss     = zipWith (\i (t, ys) -> (i, t, ys)) [-1, -2 ..] (Misc.groupList [ (t, x) | (x, t) <- vvs ])
    tyss       = zipWith (\i (t, ys) -> (i, t, ys)) [1..] (instCands ho env')
    -- Values extend term candidates, not the declarations owning sort aliases.
    env'       = List.foldl' (\e (v, t) -> F.insertSEnv v t e) env vvs
    symToSrch  = (`F.lookupSEnvWithDistance` env)
    occupied   = S.unions (map (F.sortIndices . snd) (vvs ++ F.toListSEnv env))

instSymbol :: [(SortIdx, a, [F.Symbol])] -> [(SortIdx, QualPattern)] -> [[F.Symbol]]
instSymbol tyss = go
  where
    m = M.fromList [(i, ys) | (i,_,ys) <- tyss]
    go [] =
      return []
    go ((i,qp):is) = do
      y   <- M.lookupDefault [] i m
      qsu <- maybeToList (matchSym qp y)
      ys  <- go [ (i', applyQPSubst qsu  qp') | (i', qp') <- is]
      return (y:ys)

instCands :: Bool -> F.SEnv F.Sort -> [(F.Sort, [F.Symbol])]
instCands ho env = filter isOk tyss
  where
    tyss      = Misc.groupList [(t, x) | (x, t) <- xts]
    isOk      = if ho then const True else isNothing . F.functionSort . fst
    xts       = F.toListSEnv env


type SortIdx = Int

-- | @matchP env qps@ picks, for each parameter in @qps@, a sort index among the
--   candidates paired with the parameter. Sort variables solved for one parameter
--   are applied to the remaining ones. The result is in reverse order.
matchP :: S.HashSet Int -> So.Env -> [([(SortIdx, F.Sort, a)], F.QualParam)] -> [[(SortIdx, QualPattern)]]
matchP occupied env = go []
  where
    go' !i !p !is !qps  = go ((i, p):is) qps
    go is ((tyss, qp) : qps) = do (su, i, pat) <- candidatesP (occupied `S.union` paramIndices (qp : map snd qps)) env tyss qp
                                  go' i pat is [ (tyss', applyQPP su qp') | (tyss', qp') <- qps ]
    go is []                 = return is

paramIndices :: [F.QualParam] -> S.HashSet Int
paramIndices = S.unions . map (F.sortIndices . F.qpSort)

applyQPP :: So.TVSubst -> F.QualParam -> F.QualParam
applyQPP su qp = qp
  { qpSort = So.apply     su  (qpSort qp)
  }

-- match :: So.Env -> [(F.Sort, [F.Symbol])] -> [F.Symbol] -> [F.QualParam] -> [[F.Symbol]]
-- match env tyss xs (qp : qps)
--   = do (su, qsu, x) <- candidates env tyss qp
--        match env tyss (x : xs) (applyQP su qsu <$> qps)
-- match _   _   xs []
--   = return xs

-- applyQP :: So.TVSubst -> QPSubst -> F.QualParam -> F.QualParam
-- applyQP su qsu qp = qp
--   { qpSort = So.apply     su  (qpSort qp)
--   , qpPat  = applyQPSubst qsu (qpPat qp)
--   }

--------------------------------------------------------------------------------
candidatesP ::
  S.HashSet Int ->
  So.Env ->
  [(SortIdx, F.Sort, a)] ->
  F.QualParam ->
  [(So.TVSubst, SortIdx, QualPattern)]
--------------------------------------------------------------------------------
candidatesP occupied env tyss x =
  [ (su, idx, qPat)
  | (idx, t, _) <- tyss
  , su <- maybeToList (So.unifyFastWith occupied mono env xt t)
  ]
 where
  xt = F.qpSort x
  qPat = F.qpPat x
  mono = So.isMono xt

-- --------------------------------------------------------------------------------
-- candidates :: So.Env -> [(F.Sort, [F.Symbol])] -> F.QualParam
--            -> [(So.TVSubst, QPSubst, F.Symbol)]
-- --------------------------------------------------------------------------------
-- candidates env tyss x = -- traceShow _msg
--     [(su, qsu, y) | (t, ys)  <- tyss
--                   , su       <- maybeToList (So.unifyFast mono env xt t)
--                   , y        <- ys
--                   , qsu      <- maybeToList (matchSym x y)
--     ]
--   where
--     xt   = F.qpSort x
--     mono = So.isMono xt
--     _msg = "candidates tyss :=" ++ F.showpp tyss ++ "tx := " ++ F.showpp xt

matchSym :: F.QualPattern -> F.Symbol -> Maybe QPSubst
matchSym qp y' = case qp of
  F.PatPrefix s i -> JustSub i <$> F.stripPrefix s y
  F.PatSuffix i s -> JustSub i <$> F.stripSuffix s y
  F.PatNone       -> Just NoSub
  F.PatExact s    -> if s == y then Just NoSub else Nothing
  F.PatLit        -> Nothing
  where
    y             =  F.unKArgSymbol y'

data QPSubst = NoSub | JustSub Int F.Symbol

applyQPSubst :: QPSubst -> F.QualPattern -> F.QualPattern
applyQPSubst (JustSub i x) (F.PatPrefix s j)
  | i == j = F.PatExact (F.mappendSym s x)
applyQPSubst (JustSub i x) (F.PatSuffix j s)
  | i == j = F.PatExact (F.mappendSym x s)
applyQPSubst _ p
  = p

--------------------------------------------------------------------------------
okInst :: (F.SrcSpan -> Maybe F.Sort -> F.Expr -> Maybe PJ.Doc) -> [(F.Symbol, F.Sort)] -> Sol.EQual -> Bool
--------------------------------------------------------------------------------
okInst checkAt vvs eq = isNothing (checkAt (F.srcSpan eq) Nothing (F.PAll vvs (Sol.eqPred eq)))


--------------------------------------------------------------------------------
-- | Predicate corresponding to LHS of constraint in current solution
--------------------------------------------------------------------------------
{-# SCC lhsPred #-}
lhsPred ::
    (F.Loc a) =>
    Config ->
    S.HashSet F.Symbol ->
    F.IBindEnv ->
    F.SInfo a ->
    Sol.Solution ->
    F.SimpC a ->
    F.Expr
lhsPred cfg scope bindingsInSmt info s c =
    F.notracepp _msg $ apply cfg g s bs
  where
    g = combinedEnv info scope bs (F.srcSpan c) bindingsInSmt mempty
    bs = F.senv c
    _msg = "LhsPred for id = " ++ show (sid c) ++ " with SOLUTION = " ++ F.showpp s

-- Lambda-lift eliminated definitions for one fixed solution observation.
-- Definitions are local to its SMT bracket, not shared across refinement steps.
type SummaryKey = (F.KVar, Integer, [F.BindId], [(F.Symbol, F.Sort)])
data SummaryState = SummaryState
    { summaryNext :: F.Symbol
    , summaryNames :: S.HashSet F.Symbol
    , summaryBodies :: M.HashMap F.Symbol F.Equation
    , summaryCubes :: Ordered.Map SummaryKey F.Expr
    , summaryTypes :: Ordered.Map (F.Symbol, [(F.Symbol, F.Sort)]) F.Symbol
    , summaryParameterSorts :: F.SEnv F.Sort
    , summaryFormals :: S.HashSet F.Symbol
    }
type SummaryM = St.State SummaryState

-- The SMT observation omits common witnesses; an exported closure owns its
-- complete defining environment, independently of the occurrence's scope.
type CubeScope a = CombinedEnv a -> F.KVar -> Sol.Cube -> (CombinedEnv a, F.IBindEnv)

{- | Index declarations once for a fixed, elaborated solver query. Each
observation reserves the lexical scopes and bodies it actually interprets;
preparing the state does not demand qualifier instantiation. Rebuild it when
the binding environment changes. Every observation starts with empty caches.

Sanitization removes substitutions outside each WF domain; uniqification
installs every remaining term formal in BindEnv. Only those coordinates and
lexically owned names need parameters; fixed globals remain free in definitions.
-}
prepareSummaryState ::
    S.HashSet F.Symbol ->
    F.SInfo a ->
    SummaryState
prepareSummaryState scope info = initial
  where
    initial =
        SummaryState
            (F.tempSymbol (F.symbol "eliminated_summary") 0)
            (scope `S.union` formals)
            mempty
            mempty
            mempty
            parameterSorts
            formals
    formals = S.fromList (concatMap (F.kvarDomain info) (M.keys (F.ws info)))
    be = F.bs info
    parameterSorts =
        F.fromListSEnv
            [(name, F.sr_sort refinement) | (_, (name, refinement, _)) <- F.bindEnvToList be]

-- | Compact LHS, with equation sharing confined to this observation's bracket.
lhsPredShared ::
    (F.Loc a) =>
    Config ->
    SummaryState ->
    S.HashSet F.Symbol ->
    F.IBindEnv ->
    F.SInfo a ->
    Sol.Solution ->
    F.SimpC a ->
    ([F.Equation], F.Expr)
lhsPredShared cfg initial scope known info solution constraint = (definitions, predicate)
  where
    environment = combinedEnv info scope (F.senv constraint) (F.srcSpan constraint) known mempty
    (predicate, final) = St.runState (sharedApply select cfg environment solution (F.senv constraint)) initial
    definitions = summaryDefinitions (summaryBodies final) (F.syms predicate)
    select env variable cube = (env, F.diffIBindEnv (Sol.cuBinds cube) (Misc.safeLookup "sScp" variable (Sol.sScp solution)))

summaryDefinitions :: M.HashMap F.Symbol F.Equation -> S.HashSet F.Symbol -> [F.Equation]
summaryDefinitions bodies free =
    reverse . snd $
        St.execState (mapM_ visit (S.toList free)) (S.empty, [])
  where
    visit :: F.Symbol -> St.State (S.HashSet F.Symbol, [F.Equation]) ()
    visit name = do
        seen <- St.get
        when (not (S.member name (fst seen))) $ case M.lookup name bodies of
            Nothing -> pure ()
            Just equation -> do
                St.modify (\(done, equations) -> (S.insert name done, equations))
                mapM_ visit (S.toList (equationFree equation))
                St.modify (\(done, equations) -> (done, equation : equations))

equationFree :: F.Equation -> S.HashSet F.Symbol
equationFree equation = F.syms (F.eqBody equation) `S.difference` S.fromList (map fst (F.eqArgs equation))

summaryFree :: CombinedEnv a -> F.Expr -> S.HashSet F.Symbol
summaryFree environment expression =
    F.syms expression
        `S.difference` ceInScope environment
        `S.difference` S.fromList (map fst (F.toListSEnv (ceLocalSorts environment)))

recordSummary :: CombinedEnv a -> [(F.Symbol, F.Sort)] -> F.Expr -> SummaryM F.Symbol
recordSummary environment parameters body = do
    state <- St.get
    let occupied =
            S.unions
                [ summaryNames state
                , ceInScope environment
                , ceFixed environment
                , S.fromList (map fst (F.toListSEnv (ceLocalSorts environment)) ++ map fst parameters)
                , F.syms body
                ]
        (names, name) = F.freshInNS (summaryNext state) occupied
        equation = F.mkEquation name parameters body F.boolSort
    -- Reserve free support; nested lexical owners are protected by scoped
    -- interpretation and capture-avoiding specialization, not global freshness.
    St.put state{summaryNext = name, summaryNames = names, summaryBodies = M.insert name equation (summaryBodies state)}
    pure name

dropSummaryUnsorted :: Config -> CombinedEnv a -> F.Subst -> SummaryM F.Subst
dropSummaryUnsorted cfg environment substitution = do
    equations <- St.gets summaryBodies
    let observed expression = bindSummaries equations (summaryFree environment expression) expression
    pure (dropUnsortedExprsWith observed cfg environment substitution)

bindSummaries :: M.HashMap F.Symbol F.Equation -> S.HashSet F.Symbol -> F.Expr -> F.Expr
bindSummaries equations needed expression = foldr define expression (summaryDefinitions equations needed)
  where
    define equation = F.ELet (F.eqName equation) (foldr F.ELam (F.eqBody equation) (F.eqArgs equation))

sharedApply :: CubeScope a -> Config -> CombinedEnv a -> Sol.Solution -> F.IBindEnv -> SummaryM F.Expr
sharedApply select cfg environment solution bindings =
    interpretRefts
        (\env -> sharedKVar select cfg env solution)
        environment
        (map (lookupBindEnvExt environment) (F.elemsIBindEnv bindings))

-- Interpret source predicates and actual arguments under a fixed solution.
-- Sanitization and qualifier construction ensure stored candidates are
-- KVar-free; the callback interprets eliminated definitions before returning.
-- Its image is therefore a predicate value, not another expression to expand.
interpretExpr :: (Monad m) => (CombinedEnv a -> F.KVSub -> m F.Expr) -> CombinedEnv a -> F.Expr -> m F.Expr
interpretExpr interpret original expression
    | V.isConc expression = pure expression
    | otherwise = go expression
  where
    environment = original{ceBindingsInSmt = F.emptyIBindEnv}
    under bindings =
        (bindLocalSorts bindings environment)
            { ceInScope = ceInScope environment `S.union` S.fromList (map fst bindings)
            }
    support = ceInScope environment `S.union` ceFixed environment
    shadows bindings value = any (`S.member` support) (map fst bindings) && not (V.isConc value)
    refresh value = F.substr (support `S.union` F.syms value) mempty value
    -- Refresh consumer binders before inserting a definition's free names.
    -- Rapier substitution also transports explicit and implicit KVar actuals.
    go value@(F.PAll bindings _) | shadows bindings value = go (refresh value)
    go value@(F.PExist bindings _) | shadows bindings value = go (refresh value)
    go value@(F.ELam binding _) | shadows [binding] value = go (refresh value)
    go (F.PAll bindings body) = F.PAll bindings <$> interpretExpr interpret (under bindings) body
    go (F.PExist bindings body) = F.PExist bindings <$> interpretExpr interpret (under bindings) body
    go (F.ELam binding body) = F.ELam binding <$> interpretExpr interpret (under [binding]) body
    go (F.ELet name rhs body) = do
        rhs' <- go rhs
        go
            ( F.substr
                (ceInScope environment `S.union` F.syms rhs' `S.union` F.syms body)
                (F.mkSubst [(name, rhs')])
                body
            )
    go (F.PKVar variable types arguments) =
        interpret environment (F.KVS (F.vv Nothing) F.boolSort variable arguments types)
    go (F.EApp function argument) = F.EApp <$> go function <*> go argument
    go (F.ENeg value) = F.ENeg <$> go value
    go (F.EBin operator left right) = F.EBin operator <$> go left <*> go right
    go (F.EIte condition left right) = F.EIte <$> go condition <*> go left <*> go right
    go (F.ECst value sort) = (`F.ECst` sort) <$> go value
    go (F.PAnd predicates) = F.PAnd <$> mapM go predicates
    go (F.POr predicates) = F.POr <$> mapM go predicates
    go (F.PNot predicate) = F.PNot <$> go predicate
    go (F.PImp left right) = F.PImp <$> go left <*> go right
    go (F.PIff left right) = F.PIff <$> go left <*> go right
    go (F.PAtom relation left right) = F.PAtom relation <$> go left <*> go right
    go (F.ECoerc from to value) = F.ECoerc from to <$> go value
    go (F.ETApp value sort) = (`F.ETApp` sort) <$> go value
    go (F.ETAbs value sort) = (`F.ETAbs` sort) <$> go value
    go value = pure value

sharedKVar :: CubeScope a -> Config -> CombinedEnv a -> Sol.Solution -> F.KVSub -> SummaryM F.Expr
sharedKVar select cfg environment solution =
    interpretKVar (\env -> sharedCube select cfg env solution) (dropSummaryUnsorted cfg) environment solution

sharedCube :: CubeScope a -> Config -> CombinedEnv a -> Sol.Solution -> F.KVSub -> Sol.Cube -> SummaryM F.Expr
sharedCube select cfg original solution occurrence cube = do
    let variable = F.ksuKVar occurrence
        (environment, bindings) = select original variable cube
        (ids, locals) = ceScopeKey environment
        key =
            ( variable
            , Sol.cuId cube
            , ids
            , locals
            )
    cached <- St.gets (Ordered.lookup key . summaryCubes)
    call <- case cached of
        Just value -> pure value
        Nothing -> do
            let quantified = symSorts environment bindings
            predicate <-
                F.pExist quantified . F.pAndNoDedup
                    <$> cubeConjuncts
                        environment
                        (\env -> sharedKVar select cfg env solution)
                        (dropSummaryUnsorted cfg)
                        cube
                        bindings
                        quantified
            parameterSorts <- St.gets summaryParameterSorts
            formals <- St.gets summaryFormals
            let available = combinedSEnv environment
                lookupSort name = F.lookupSEnv name available `mplus` F.lookupSEnv name parameterSorts
                free = F.syms predicate
                -- Fixed globals retain their occurrence-specific instances.
                isLocal name = F.memberSEnv name (ceLocalSorts environment) || S.member name formals
                parameters = List.sort [(name, sort) | name <- S.toList free, isLocal name, sort <- maybeToList (lookupSort name)]
                missing = [name | name <- S.toList free, S.member name formals, isNothing (lookupSort name)]
            when (not (null missing)) $
                Misc.errorstar ("lhsPredShared requires normalized typed formals: " ++ show missing)
            definitions <- St.gets summaryBodies
            let definedSort equation = foldr F.FFunc (F.eqSort equation) (map snd (F.eqArgs equation))
                declarations = F.fromListSEnv [(F.eqName equation, definedSort equation) | equation <- M.elems definitions] <> declarationSEnv environment
                localSorts = F.fromListSEnv parameters <> ceLocalSorts environment
                -- Build the complete witness relation first. Projection then
                -- substitutes only checked defining equalities, preserving
                -- every witness constraint without duplicating equal calls.
                projected = simplifyKVar declarations localSorts predicate
            name <- recordSummary original parameters projected
            let value = F.eApps (F.EVar name) (map (F.EVar . fst) parameters)
            St.modify (\state -> state{summaryCubes = Ordered.insert key value (summaryCubes state)})
            pure value
    specializeSummary original (F.ksuTySub occurrence) call

specializeSummary :: CombinedEnv a -> F.TyVarSubst -> F.Expr -> SummaryM F.Expr
specializeSummary environment original expression
    | M.null types = pure expression
    | otherwise = do
        substitution <- renames (summaryFree environment typed)
        pure (F.subst substitution typed)
  where
    types = M.filterWithKey (\name sort -> sort /= F.FObj name) original
    typed = V.applyCoSub types expression
    renames free = do
        equations <- St.gets summaryBodies
        F.mkSubst <$> traverse specialize [(name, body) | name <- S.toList free, Just body <- [M.lookup name equations]]
    specialize (name, body) = do
        let key = (name, List.sort (M.toList types))
        previous <- St.gets (Ordered.lookup key . summaryTypes)
        specialized <- case previous of
            Just result -> pure result
            Nothing -> do
                let typedBody = body{F.eqArgs = map (second (F.sortSubst types)) (F.eqArgs body), F.eqBody = V.applyCoSub types (F.eqBody body)}
                substitution <- renames (equationFree typedBody)
                let fresh = F.subst substitution typedBody
                result <- recordSummary environment (F.eqArgs fresh) (F.eqBody fresh)
                St.modify (\state -> state{summaryTypes = Ordered.insert key result (summaryTypes state)})
                pure result
        pure (name, F.EVar specialized)

data CombinedEnv a = CEnv
    { ceInfo :: !(F.SInfo a)
    , ceInScope :: !(S.HashSet F.Symbol)
    , ceIEnv :: !F.IBindEnv
    , ceSpan :: !F.SrcSpan
    , ceBindingsInSmt :: !F.IBindEnv
    {- ^ These are the bindings that the smt solver knows about and can be
    referred as @EVar (bindSymbol <bindId>)@ instead of serializing them
    again.
    -}
    , ceLocalSorts :: !(F.SEnv F.Sort)
    , ceFixed :: S.HashSet F.Symbol
    , declarationSEnv :: F.SEnv F.Sort
    , ceScopeKey :: ([F.BindId], [(F.Symbol, F.Sort)])
    }

-- Declaration lookup and canonical identity belong to the scope, not each use.
-- Keep these projections lazy when an observation does not need them.
combinedEnv :: F.SInfo a -> S.HashSet F.Symbol -> F.IBindEnv -> F.SrcSpan -> F.IBindEnv -> F.SEnv F.Sort -> CombinedEnv a
combinedEnv info scope ids location known locals =
    CEnv info scope ids location known locals fixed declarations (List.sort (F.elemsIBindEnv ids), List.sort (F.toListSEnv locals))
  where
    declarations = F.sr_sort <$> F.fromListSEnv (F.envCs (F.bs info) ids)
    -- Explicit query declarations own their names even when BindEnv repeats
    -- them. Ambient built-ins are not declarations of a query-local witness.
    fixed = S.fromList (map fst (F.toListSEnv (F.gLits info <> F.dLits info)) ++ map fst (F.toListSEnv defined))
    defined = Thy.theorySymbols (F.ddecls info) <> Thy.theorySymbols (F.defns info) <> Thy.theorySymbols (F.aenvEqs (F.ae info))

bindLocalSorts :: [(F.Symbol, F.Sort)] -> CombinedEnv a -> CombinedEnv a
bindLocalSorts bindings environment =
    environment
        { ceLocalSorts = locals
        , ceScopeKey = (fst (ceScopeKey environment), List.sort (F.toListSEnv locals))
        }
  where
    locals = F.fromListSEnv bindings <> ceLocalSorts environment

apply :: Config -> CombinedEnv ann -> Sol.Sol Sol.QBind -> F.IBindEnv -> F.Expr
apply cfg g s bs =
    runIdentity $
        interpretRefts
            (\env -> Identity . applyKVar cfg env s)
            g
            (map (lookupBindEnvExt g) (F.elemsIBindEnv bs))

-- | @applyInSortedReft@ applies the solution to a single sorted reft
applyInSortedReft ::
    Config ->
    CombinedEnv ann ->
    Sol.Sol Sol.QBind ->
    (F.Symbol, F.SortedReft) ->
    (F.Symbol, F.SortedReft)
applyInSortedReft cfg g s xsr@(x, sr) =
    let predicate = runIdentity $ interpretRefts (\env -> Identity . applyKVar cfg env s) g [xsr]
     in (x, sr{F.sr_reft = F.Reft (x, predicate)})

interpretRefts :: (Monad m) => (CombinedEnv a -> F.KVSub -> m F.Expr) -> CombinedEnv a -> [(F.Symbol, F.SortedReft)] -> m F.Expr
interpretRefts interpret environment refinements = do
    let (concrete, variables) = envConcKVars refinements
    -- KVar bodies bind their own variables and require the full predicates.
    applied <- mapM (interpret environment{ceBindingsInSmt = F.emptyIBindEnv}) variables
    concrete' <- mapM (interpretExpr interpret environment) concrete
    pure (F.conj (F.pAndNoDedup applied : concrete'))

-- | Produces conjuncts of each sorted reft in the IBindEnv, separated
-- into concrete conjuncts and kvars.
envConcKVars :: [(F.Symbol, F.SortedReft)] -> ([F.Expr], [F.KVSub])
envConcKVars xrs =
  let (pss, kss) = unzip [ F.sortedReftConcKVars x sr | (x, sr) <- xrs ]
   in (concat pss, concat kss)

lookupBindEnvExt
  :: CombinedEnv ann -> F.BindId -> (F.Symbol, F.SortedReft)
lookupBindEnvExt g i =
     (,) x $
       if F.memberIBindEnv i (ceBindingsInSmt g)
       then sr { F.sr_reft = F.Reft (x, F.EVar (F.bindSymbol (fromIntegral i)))}
       else sr
   where
      (x, sr, _)              = F.lookupBindEnv i (F.bs (ceInfo g))

applyKVar :: Config -> CombinedEnv ann -> Sol.Sol Sol.QBind -> F.KVSub -> F.Expr
applyKVar cfg environment solution =
    runIdentity
        . interpretKVar
            (\env occurrence -> Identity . cubePred cfg env solution occurrence)
            (\env -> Identity . dropUnsortedExprs cfg env)
            environment
            solution

-- Both observations interpret actuals before applying a fixed solution. Only
-- cube representation and its sort observation differ: direct predicates, or
-- calls whose definitions must also be in scope for checking an actual.
interpretKVar ::
    (Monad m) =>
    (CombinedEnv a -> F.KVSub -> Sol.Cube -> m F.Expr) ->
    (CombinedEnv a -> F.Subst -> m F.Subst) ->
    CombinedEnv a ->
    Sol.Solution ->
    F.KVSub ->
    m F.Expr
interpretKVar observeCube sorted environment solution original = do
    let domain = S.fromList (F.kvarDomain (ceInfo environment) (F.ksuKVar original))
        -- Binder refresh can add implicit actuals outside this interface.
        argumentsInDomain = M.filterWithKey (\name _ -> S.member name domain) (F.fromKVarSubst (F.ksuSubst original))
    arguments <- F.toKVarSubst <$> traverse interpret argumentsInDomain
    let occurrence = original{F.ksuSubst = arguments}
    case Sol.lookup solution (F.ksuKVar occurrence) of
        Right qualifiers ->
            pure (F.pAndNoDedup (map fst (qbPreds (F.substFromKSubst arguments) (F.ksuTySub occurrence) qualifiers)))
        Left [] -> pure (F.pOr [])
        Left cubes -> do
            -- Later cubes only add fresh definitions, so this judgment is fixed.
            actuals <- sorted environment (F.substFromKSubst arguments)
            let occupied = ceInScope environment `S.union` F.substSymbolsSet actuals
                -- Either side can mention freshly generated summary names.
                instantiate body = F.substr (occupied `S.union` F.syms body) actuals body
            F.pOr . map instantiate <$> mapM (observeCube environment occurrence) cubes
  where
    interpret = interpretExpr (\env -> interpretKVar observeCube sorted env solution) environment

-- Interpret Boolean predicate arguments using the current solution, before
-- substituting them into a qualifier or eliminated definition.
applyExpr :: Config -> CombinedEnv ann -> Sol.Sol Sol.QBind -> F.Expr -> F.Expr
applyExpr cfg environment solution =
    runIdentity . interpretExpr (\env -> Identity . applyKVar cfg env solution) environment

qbPreds :: F.Subst -> F.TyVarSubst -> Sol.QBind -> [(F.Pred, Sol.EQual)]
qbPreds su tvsu (Sol.QB eqs) =
  [ (F.subst su $ V.applyCoSub tvsu $ Sol.eqPred eq, eq) | eq <- eqs ]

nonCutsResult :: Config -> S.HashSet F.Symbol -> F.SInfo ann -> Sol.Sol Sol.QBind -> FixDelayedSolution
nonCutsResult cfg scope info solution = M.mapWithKey (\variable _ -> Delayed (export variable)) (Sol.sHyp solution)
  where
    g = combinedEnv info scope F.emptyIBindEnv F.dummySpan F.emptyIBindEnv mempty
    initial = prepareSummaryState scope info
    export variable =
        let occurrence = F.KVS (F.vv Nothing) F.boolSort variable (F.toKVarSubst M.empty) mempty
            (predicate, final) = St.runState (sharedKVar select cfg g solution occurrence) initial
         in bindSummaries (summaryBodies final) (F.syms predicate) predicate
    -- A defining cube is a complete constraint environment. Its body and
    -- actual admission use that environment, not an ancestor's witnesses.
    -- Keep every equality and close every witness at EVERY nested definition
    -- (including common sScp binders; see upstream issue #808).
    select environment _ cube =
        ( (combinedEnv info scope bindings (ceSpan environment) F.emptyIBindEnv mempty){ceFixed = ceFixed environment}
        , bindings
        )
      where
        bindings = Sol.cuBinds cube

{- | At the moment, the liquid-fixpoint implementation allows for unsorted
expressions in substitutions. See the discussion in
https://github.com/ucsd-progsys/liquid-fixpoint/issues/800
The `explicitKvars` flag is meant for Horn-style constraints, which must
have well-formed (expressions) as arguments, and so we *disable* the
-}
-- filtering of unsorted expressions when that flag is set.
dropUnsortedExprs :: Config -> CombinedEnv ann -> F.Subst -> F.Subst
dropUnsortedExprs = dropUnsortedExprsWith id

-- Admission observes a value, independently of whether its representation
-- contains shared definitions. Only the observation changes the judgment.
dropUnsortedExprsWith :: (F.Expr -> F.Expr) -> Config -> CombinedEnv ann -> F.Subst -> F.Subst
dropUnsortedExprsWith observe cfg g su@(F.Su m)
    | explicitKvars cfg = su
    | otherwise = F.Su (M.filter (maybe False (not . isClass) . checkAt . observe) m)
  where
    checkAt = either (const Nothing) Just . So.sortExprE (Just (symbolEnv cfg (ceInfo g))) (ceSpan g) (declarationSEnv g) (ceLocalSorts g)

{- | `cubePred g s ksu c` returns the type-specialized predicate
      defined by using cube

        c := [b1,...,bn] |- (k . su')

      in the binder environment `g`. The binders in `sScp s k` are not included
      in the final predicate. They are considered redundant conjuncts as per
      section 2.4 of "Local Refinement Typing", ICFP 2017.
      `interpretKVar` then applies the occurrence's term arguments.
 -}
cubePred :: Config -> CombinedEnv ann -> Sol.Sol Sol.QBind -> F.KVSub -> Sol.Cube -> F.Expr
cubePred cfg g s ksu c =
    V.applyCoSub (F.ksuTySub ksu) . F.pExist quantified . F.pAndNoDedup $
        runIdentity $
            cubeConjuncts g (\env -> Identity . applyKVar cfg env s) (\env -> Identity . dropUnsortedExprs cfg env) c bs' quantified
  where
    bs' = F.diffIBindEnv bs (Misc.safeLookup "sScp" k (Sol.sScp s))
    bs = Sol.cuBinds c
    k = F.ksuKVar ksu
    quantified = symSorts g bs'

-- | @cubeConjuncts@ computes the body conjuncts for the selected defining binders.
--
-- Schematically, the result is
--
-- > Exists (bindsOf bs'). (pAnd (predicatesOf bs'))[Sol.cuSubst c]
--
-- but we also preserve the information about which variables are being
-- substituted:
--
-- > Exists (bindsOf bs'). pAnd (predicatesOf bs') && x1=e1 && ... && xn=en
--
-- where @Sol.cuSubst c = [x1:=e1;...;xn:=en]@. The caller conjoins and
-- quantifies these predicates; reports deduplicate before quantification.
--
cubeConjuncts ::
    (Monad m) =>
    CombinedEnv a ->
    (CombinedEnv a -> F.KVSub -> m F.Expr) ->
    (CombinedEnv a -> F.Subst -> m F.Subst) ->
    Sol.Cube ->
    F.IBindEnv ->
    [(F.Symbol, F.Sort)] ->
    m [F.Expr]
cubeConjuncts environment interpret sorted cube bindings quantified = do
    predicate <- interpretRefts interpret inside (map (lookupBindEnvExt inside) (F.elemsIBindEnv bindings))
    let F.Su original = Sol.cuSubst cube
    values <- traverse (interpretExpr interpret inside) original
    F.Su substitutions <- sorted inside (F.Su values)
    let equalities = F.pAnd [F.EEq (F.EVar name) value | (name, value) <- M.toList substitutions]
    pure [predicate, equalities]
  where
    -- The existential binders own these names in both defining predicates and
    -- substitutions, including while nested definitions are interpreted.
    inside = bindLocalSorts quantified (addCEnv environment (Sol.cuBinds cube))

isClass :: F.Sort -> Bool
isClass F.FNum  = True
isClass F.FFrac = True
isClass _       = False

combinedSEnv :: CombinedEnv a -> F.SEnv F.Sort
combinedSEnv g = ceLocalSorts g <> declarationSEnv g

addCEnv :: CombinedEnv a -> F.IBindEnv -> CombinedEnv a
addCEnv g bs' =
    (combinedEnv (ceInfo g) (ceInScope g) (F.unionIBindEnv (ceIEnv g) bs') (ceSpan g) (ceBindingsInSmt g) (ceLocalSorts g))
        { ceFixed = ceFixed g
        }

symSorts :: CombinedEnv a -> F.IBindEnv -> [(F.Symbol, F.Sort)]
symSorts g bs = [(name, F.sr_sort refinement) | (name, refinement) <- F.envCs (F.bs (ceInfo g)) bs, not (S.member name (ceFixed g))]

_noKvars :: F.Expr -> Bool
_noKvars = null . V.kvarsExpr

{- | Project existential witnesses without changing source sorts or free names.
The declarations own type coordinates; the separate telescope contains the
canonical KVar parameters. Logical sorts are inhabited, so unused witnesses
may be dropped and independent conjuncts may leave their quantifier.
-}
simplifyKVar :: F.SEnv F.Sort -> F.SEnv F.Sort -> F.Expr -> F.Expr
simplifyKVar declarations locals = conjoin . floatConjuncts locals . go locals
  where
    go env (F.POr es) = disj $ map (conjoin . floatConjuncts env . go env) es
    go env (F.PAnd es) = conjoin $ concatMap (floatConjuncts env . go env) es
    go env (F.PExist bs e) = project env bs (go (bind bs env) e)
    go _ e = e

    conjoin = F.conj . List.nubBy (alphaEq S.empty)
    disj [] = F.PFalse
    disj [e] = e
    disj es = F.POr es
    bind bs env = F.fromListSEnv (reverse bs) <> env

    project env bs (F.PExist inner e) =
        project env (filter ((`notElem` map fst inner) . fst) bs ++ inner) e
    project env bs e =
        case break (isJust . fst) [(witness clause, clause) | clause <- clauses] of
            (before, (Just binding, _) : after) ->
                project env bs (F.subst1 (F.conj (map snd before ++ map snd after)) binding)
            _ -> F.pExist (filter ((`S.member` F.syms residual) . fst) bs) residual
      where
        clauses = conjuncts (bind bs env) e
        residual = F.conj clauses
        infer = So.sortExprE Nothing F.dummySpan declarations (bind bs env)
        witness (F.PAtom F.Eq left right) = orient left right `mplus` orient right left
        witness _ = Nothing
        orient variable replacement = do
            (name, sort) <- boundVariable variable
            guard (not (S.member name (F.syms replacement)))
            actual <- either (const Nothing) Just (infer replacement)
            guard (sourceIdentity (close actual) sort)
            pure (name, ascribe sort replacement)
        boundVariable (F.EVar name) = (name,) . close <$> List.lookup name bs
        boundVariable (F.ECst expression sort) = do
            binding@(_, source) <- boundVariable expression
            guard (sourceIdentity (close sort) source)
            pure binding
        boundVariable _ = Nothing

    close = F.resolveNumericSort (`F.lookupSEnv` declarations)
    -- Primitive sorts have no metadata to preserve. Other witnesses retain the
    -- eliminated variable's numeric-capability annotations without forcing them.
    ascribe F.FInt e = e
    ascribe F.FReal e = e
    ascribe sort e = F.ECst e sort

    conjuncts env = filter (not . trivial) . F.splitPAnd
      where
        trivial F.PTrue = True
        trivial F.PTop = True
        trivial (F.PAtom F.Eq left right) = sourceIdentity (identityCast left) (identityCast right)
        trivial _ = False
        -- This is only an equality proof, not a rewrite of the retained term.
        -- Read the variable's uninstantiated sort: opening a declaration scheme
        -- here would forget which occurrence-specific type application was used.
        identityCast (F.ECst e sort)
            | S.null (F.sortIndices (close sort))
            , variable@(F.EVar name) <- identityCast e
            , Just source <- F.lookupSEnv name env `mplus` F.lookupSEnv name declarations
            , sourceIdentity (close source) (close sort) =
                variable
        identityCast e = e

    floatConjuncts env original@(F.PExist bs e)
        | null independent = [original]
        | otherwise = conjuncts env (project env bs (F.conj dependent)) ++ independent
      where
        names = S.fromList (map fst bs)
        (independent, dependent) = List.partition (S.null . S.intersection names . F.syms) (conjuncts (bind bs env) e)
    floatConjuncts env e = conjuncts env e

-- Nominal Sort/Expr equality ignores all TCInfo. Only its string flag changes
-- the SMT carrier; numeric capability remains in retained source annotations.
-- Stop before the other metadata fields: LH may leave them unevaluated.
sourceIdentity :: (Eq a, Generics.Data a) => a -> a -> Bool
sourceIdentity left right = left == right && all ((== 1) . S.size) evidence
  where
    -- Require one carrier per nominal constructor across both values. This is
    -- conservative for mixed metadata and independent of map traversal order.
    evidence = M.unionWith S.union (carriers left) (carriers right)
    carriers =
        Generics.everythingBut (M.unionWith S.union) $
            Generics.mkQ (M.empty, False) constructor
                `Generics.extQ` (atom :: F.Symbol -> (M.HashMap F.Symbol (S.HashSet Bool), Bool))
                `Generics.extQ` (atom :: Text.Text -> (M.HashMap F.Symbol (S.HashSet Bool), Bool))
                `Generics.extQ` (atom :: String -> (M.HashMap F.Symbol (S.HashSet Bool), Bool))
    constructor tc = (M.singleton (F.val (F.fTyconSymbol tc)) (S.singleton (F.isString (F.FTC tc))), True)
    atom _ = (M.empty, True)

{- | Sound, deliberately partial alpha comparison for solution conjunctions.
Both existential telescopes use the same fresh names, preserving free names,
binder arity, and source sorts. Other syntax is compared structurally.
-}
alphaEq :: S.HashSet F.Symbol -> F.Expr -> F.Expr -> Bool
alphaEq scope left right = go (S.unions [scope, F.syms left, F.syms right]) left right
  where
    go :: S.HashSet F.Symbol -> F.Expr -> F.Expr -> Bool
    go names (F.PExist bs1 e1) (F.PExist bs2 e2)
        | sourceIdentity (map snd bs1) (map snd bs2) =
            let (inside, fresh) = F.freshInNSL (map fst bs1) (S.unions [names, F.syms e1, F.syms e2])
                rename bs = F.subst (F.mkSubst (zip (map fst bs) (map F.EVar fresh)))
             in go inside (rename bs1 e1) (rename bs2 e2)
        | otherwise = False
    go names (F.PAnd es1) (F.PAnd es2) = sameChildren names es1 es2
    go names (F.POr es1) (F.POr es2) = sameChildren names es1 es2
    go _ e1 e2 = sourceIdentity e1 e2
    sameChildren names es1 es2 = length es1 == length es2 && and (zipWith (go names) es1 es2)

--------------------------------------------------------------------------------
-- | Save Solution to File -----------------------------------------------------
--------------------------------------------------------------------------------

saveSolution :: Config -> String -> Result a -> IO ()
saveSolution cfg sfx res = when (save cfg) $ do
  let f = Files.tempFileName (srcFile cfg ++ sfx ++ ".fqout")
  putStrLn $ "Saving Solution: " ++ f ++ "\n"
  ensurePath f
  writeFile f $ unlines $
    [ ""
    , "Solution:"
    , scopedRender (resSolution  res)
    ] ++
    [ ""
    , ""
    , "Non-cut kvars:"
    , ""
    , scopedRender (M.map forceDelayed $ resNonCutsSolution res)
    ]
    where
      -- Lexical definitions preserve sharing, but page-layout indentation can
      -- itself grow quadratically with their depth. Keep every token without
      -- padding each nested definition to its parent column.
      scopedRender = PJ.renderStyle PJ.style{PJ.mode = PJ.LeftMode} . PJ.vcat . map ncDoc . scoped
      scoped sol = [(k, scope k, So.unApply e) | (k, e) <- M.toList sol]
      scope k = [(formalCanonical f, formalSort f) | f <- M.lookupDefault [] k (resScopes res)]
      ncDoc (k, xts, e) = PJ.hsep [ F.pprint k PJ.<> F.pprint xts, PJ.text ":=", F.pprint e ]
