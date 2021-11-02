--------------------------------------------------------------------------------
-- | This module is a preliminary part of the implementation of "Proof by 
--   Logical Evaluation" where we unfold function definitions if they *must* be 
--   unfolded, to strengthen the environments with function-definition-equalities. 
--   In this module, we use an interpreter in Haskell to attempt to evaluate down
--   expressions and generate equalities.
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language.Fixpoint.Solver.Interpreter (instInterpreter) where

import           Language.Fixpoint.Types hiding (simplify)
import           Language.Fixpoint.Types.Config  as FC
import qualified Language.Fixpoint.Types.Visitor as Vis
import qualified Language.Fixpoint.Misc          as Misc 
import           Language.Fixpoint.Smt.Theories
import           Language.Fixpoint.Defunctionalize
import qualified Language.Fixpoint.Utils.Trie    as T 
import           Language.Fixpoint.Utils.Progress 
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Graph.Deps             (isTarget) 
import           Language.Fixpoint.Solver.Sanitize        (symbolEnv)
import           Language.Fixpoint.Solver.Rewrite
import           Control.Monad.State
import           Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb
--import           Debug.Trace                              (trace)

mytracepp :: (PPrint a) => String -> a -> a
mytracepp = notracepp 

mytrace :: String -> a -> a
mytrace = {-trace-} flip const

--------------------------------------------------------------------------------
-- | Strengthen Constraint Environments via PLE 
--------------------------------------------------------------------------------
instInterpreter :: (Loc a) => Config -> SInfo a -> Maybe [SubcId] -> IO (SInfo a)
instInterpreter cfg fi' subcIds = do
    let cs = [ (i, c) | (i, c) <- M.toList (cm fi), isPleCstr aEnv i c,
               maybe True (i `L.elem`) subcIds ]
    let t  = mkCTrie {-cs --} $ mytrace (showQueryBE fi ++ "\n\nconstraints " ++ L.foldl' (\acc (_,c) -> acc ++ showSimpC c) "" cs) cs                                               -- 1. BUILD the Trie
    res   <- withProgress (1 + length cs) $ 
               pleTrie t $ instEnv cfg fi cs sEnv  -- 2. TRAVERSE Trie to compute InstRes
    return $ resSInfo cfg sEnv fi $ mytracepp "final instres:   " res                                 -- 3. STRENGTHEN SInfo using InstRes
  where
    sEnv   = symbolEnv cfg fi
    aEnv   = ae fi 
    fi     = normalize fi' 

showSimpC :: SimpC a -> String
showSimpC c = "id: " ++ show (sid c) ++ "  bind: " ++ show (cbind c) ++ "\nWith binds: " ++ showpp (senv c) ++ "\nrhs: " ++ showpp (crhs c) ++ "\n\n"

showQueryBE :: SInfo a -> String
showQueryBE fi = "query bindenv " ++ showpp (bs fi)

------------------------------------------------------------------------------- 
-- | Step 1a: @instEnv@ sets up the incremental-PLE environment 
instEnv :: (Loc a) => Config -> SInfo a -> [(SubcId, SimpC a)] -> SymEnv -> InstEnv a 
instEnv cfg fi cs sEnv = InstEnv cfg bEnv aEnv cs γ s0
  where
    csBinds           = L.foldl' (\acc (_,c) -> unionIBindEnv acc (senv c)) emptyIBindEnv cs
    bEnv              = filterBindEnv (\i _ _ -> memberIBindEnv i csBinds) (bs fi)
    aEnv              = ae fi
    γ                 = knowledge cfg fi  
    s0                = EvalEnv sEnv mempty 

---------------------------------------------------------------------------------------------- 
-- | Step 1b: @mkCTrie@ builds the @Trie@ of constraints indexed by their environments 
mkCTrie :: [(SubcId, SimpC a)] -> CTrie 
mkCTrie ics  = mytracepp ("the trie is:   ") $ T.fromList [ (cBinds c, i) | (i, c) <- ics ]
  where
    cBinds   = L.sort . elemsIBindEnv . senv 

---------------------------------------------------------------------------------------------- 
-- | Step 2: @pleTrie@ walks over the @CTrie@ to actually do the incremental-PLE
pleTrie :: CTrie -> InstEnv a -> IO InstRes   
pleTrie t env = loopT env ctx0 diff0 Nothing res0 t 
  where 
    diff0        = []
    res0         = M.empty 
    ctx0         = initCtx env ((mkEq <$> es0) ++ (mkEq' <$> es0'))
    es0          = L.filter (null . eqArgs) (aenvEqs   . ieAenv $ env)
    es0'         = L.filter (null . smArgs) (aenvSimpl . ieAenv $ env)
    mkEq  eq     = (EVar $ eqName eq, eqBody eq)
    mkEq' rw     = (EApp (EVar $ smName rw) (EVar $ smDC rw), smBody rw)

loopT :: InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CTrie -> IO InstRes
loopT env ctx delta i res t = case t of 
  T.Node []  -> return res
  T.Node [b] -> loopB env ctx delta i res b
  T.Node bs  -> (withAssms env ctx delta Nothing $ \ctx' -> do 
                  (ctx'', res') <- ple1 env ctx' i res 
                  foldM (loopB env ctx'' [] i) res' bs)

loopB :: InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CBranch -> IO InstRes
loopB env ctx delta iMb res b = case b of 
  T.Bind i t -> loopT env ctx (i:delta) (Just i) res t
  T.Val cid  -> withAssms env ctx delta (Just cid) $ \ctx' -> do 
                  progressTick
                  (snd <$> ple1 env ctx' iMb res) 


withAssms :: InstEnv a -> ICtx -> Diff -> Maybe SubcId -> (ICtx -> IO b) -> IO b 
withAssms env@(InstEnv {..}) ctx delta cidMb act = do 
  let ctx'  = updCtx env ctx delta cidMb
  act ctx' 

-- | @ple1@ performs the PLE at a single "node" in the Trie 
ple1 :: InstEnv a -> ICtx -> Maybe BindId -> InstRes -> IO (ICtx, InstRes)
ple1 (InstEnv {..}) ctx i res = 
  updCtxRes (mytracepp ("\nInstRes:  ") res) i <$> evalCandsLoop {-anfEnv-} M.empty ieCfg ctx ieKnowl ieEvEnv res
{-    where
      anfBEnv = filterBindEnv anfFilter ieBEnv 
      anfFilter = (\i sym r -> (anfPrefix `isPrefixOfSym` sym) || (vvName `isPrefixOfSym` sym))

      anfEnv = M.fromList ( Mb.mapMaybe unElabRefts (M.elems (beBinds anfBEnv)) )

      unElabRefts (sym, sr) = let r = sr_reft sr in
                                (,) (EVar sym) <$> (unElab <$> isSingletonE (reftBind r) (reftPred r))-}

evalCandsLoop :: ConstMap -> Config -> ICtx -> Knowledge -> EvalEnv -> InstRes -> IO ICtx 
evalCandsLoop ie _ ictx0 γ env res = go ictx0 
  where
    withRewrites exprs =
      let
        rws = [rewrite e rw | rw <- snd <$> M.toList (knSims γ)
                            ,  e <- S.toList (snd `S.map` exprs)]
      in 
        exprs <> (S.fromList $ concat rws)
    go ictx | S.null (icCands ictx) = return ictx 
    go ictx =  do let cands = icCands ictx
                  let env' = env { evAccum = icEquals ictx <> evAccum env }
                  (ictx', evalResults)  <- 
                               foldM (evalOneCandStep ie γ env' res) (ictx, []) (S.toList cands) 
                  let us = mconcat evalResults 
                  if S.null (us `S.difference` icEquals ictx)
                        then return ictx 
                        else do  let oks      = fst `S.map` us
                                 let us'      = withRewrites us 
                                 let ictx''   = ictx' { icSolved = icSolved ictx <> oks 
                                                      , icEquals = icEquals ictx <> us' }
                                 let newcands = mconcat (makeCandidates γ ictx'' <$> S.toList (cands <> (snd `S.map` us)))
                                 go (ictx'' { icCands = S.fromList newcands})
                                 
-- evalOneCands :: Knowledge -> EvalEnv -> ICtx -> [Expr] -> IO (ICtx, [EvAccum])
-- evalOneCands γ env' ictx = foldM step (ictx, [])
evalOneCandStep :: ConstMap -> Knowledge -> EvalEnv -> InstRes -> (ICtx, [EvAccum]) -> Expr -> IO (ICtx, [EvAccum])
evalOneCandStep env γ env' inres (ictx, acc) e = do 
  res <- evalOne env γ env' ictx inres e 
  return (ictx, res : acc)

rewrite :: Expr -> Rewrite -> [(Expr,Expr)] 
rewrite e rw = Mb.catMaybes $ map (`rewriteTop` rw) (notGuardedApps e)

rewriteTop :: Expr -> Rewrite -> Maybe (Expr,Expr) 
rewriteTop e rw
  | (EVar f, es) <- splitEApp e
  , f == smDC rw
  , length es == length (smArgs rw)
  = Just (EApp (EVar $ smName rw) e, subst (mkSubst $ zip (smArgs rw) es) (smBody rw))
  | otherwise  
  = Nothing

---------------------------------------------------------------------------------------------- 
-- | Step 3: @resSInfo@ uses incremental PLE result @InstRes@ to produce the strengthened SInfo 
---------------------------------------------------------------------------------------------- 

resSInfo :: Config -> SymEnv -> SInfo a -> InstRes -> SInfo a
resSInfo cfg env fi res = strengthenBinds fi res' 
  where
    res'     = M.fromList $ zip is ps''
    ps''     = zipWith (\i -> elaborate (atLoc dummySpan ("PLE1 " ++ show i)) env) is ps' 
    ps'      = defuncAny cfg env ps
    (is, ps) = unzip (M.toList res)

---------------------------------------------------------------------------------------------- 
-- | @InstEnv@ has the global information needed to do PLE
---------------------------------------------------------------------------------------------- 

data InstEnv a = InstEnv 
  { ieCfg   :: !Config
  , ieBEnv  :: !BindEnv
  , ieAenv  :: !AxiomEnv 
  , ieCstrs :: ![(SubcId, SimpC a)]
  , ieKnowl :: !Knowledge
  , ieEvEnv :: !EvalEnv
  } 

---------------------------------------------------------------------------------------------- 
-- | @ICtx@ is the local information -- at each trie node -- obtained by incremental PLE
---------------------------------------------------------------------------------------------- 

data ICtx    = ICtx 
  { icAssms    :: S.HashSet Pred            -- ^ Equalities converted to SMT format
  , icCands    :: S.HashSet Expr            -- ^ "Candidates" for unfolding
  , icEquals   :: EvAccum                   -- ^ Accumulated equalities
  , icSolved   :: S.HashSet Expr            -- ^ Terms that we have already expanded
  , icSimpl    :: !ConstMap                 -- ^ Map of expressions to constants
  , icSubcId   :: Maybe SubcId              -- ^ Current subconstraint ID
  } 

---------------------------------------------------------------------------------------------- 
-- | @InstRes@ is the final result of PLE; a map from @BindId@ to the equations "known" at that BindId
---------------------------------------------------------------------------------------------- 

type InstRes = M.HashMap BindId Expr

---------------------------------------------------------------------------------------------- 
-- | @Unfold is the result of running PLE at a single equality; 
--     (e, [(e1, e1')...]) is the source @e@ and the (possible empty) 
--   list of PLE-generated equalities (e1, e1') ... 
---------------------------------------------------------------------------------------------- 

type CTrie   = T.Trie   SubcId
type CBranch = T.Branch SubcId
type Diff    = [BindId]    -- ^ in "reverse" order

initCtx :: InstEnv a -> [(Expr,Expr)] -> ICtx
initCtx _   es   = ICtx 
  { icAssms  = mempty 
  , icCands  = mempty 
  , icEquals = S.fromList es
  , icSolved = mempty
  , icSimpl  = mempty 
  , icSubcId = Nothing
  }

equalitiesPred :: S.HashSet (Expr, Expr) -> [Expr]
equalitiesPred eqs = [ EEq e1 e2 | (e1, e2) <- S.toList eqs, e1 /= e2 ] 

updCtxRes :: InstRes -> Maybe BindId -> ICtx -> (ICtx, InstRes) 
updCtxRes res iMb ctx = (ctx, res')
  where 
    res' = updRes res iMb (pAnd $ equalitiesPred $ icEquals ctx)


updRes :: InstRes -> Maybe BindId -> Expr -> InstRes
updRes res (Just i) e = M.insert i e res 
updRes res  Nothing _ = res 


---------------------------------------------------------------------------------------------- 
-- | @updCtx env ctx delta cidMb@ adds the assumptions and candidates from @delta@ and @cidMb@ 
--   to the context. 
---------------------------------------------------------------------------------------------- 

updCtx :: InstEnv a -> ICtx -> Diff -> Maybe SubcId -> ICtx 
updCtx (InstEnv {..}) ctx delta cidMb 
    = ctx { icCands  = S.fromList cands           <> icCands  ctx
          , icEquals = initEqs                    <> icEquals ctx
                    , icSimpl  = M.fromList (S.toList sims) <> icSimpl ctx <> econsts
                    , icSubcId = fst <$> L.find (\(_, b) -> (head delta) `memberIBindEnv` (_cenv b)) ieCstrs
                    }
  where         
    initEqs   = S.fromList $ concat [rewrite e rw | e  <- cands ++ (snd <$> S.toList (icEquals ctx))
                                                  , rw <- snd <$> M.toList (knSims ieKnowl)]
    cands     = concatMap (makeCandidates ieKnowl ctx) (rhs:es)
    sims      = S.filter (isSimplification (knDCs ieKnowl)) (initEqs <> icEquals ctx)
    econsts   = M.fromList $ findConstants ieKnowl es
    --bs        = unElab <$> binds
    (rhs:es)  = unElab <$> (eRhs : (expr <$> binds))
    eRhs      = maybe PTrue crhs subMb
    binds     = [ lookupBindEnv i ieBEnv | i <- delta ] 
    subMb     = getCstr (M.fromList ieCstrs) <$> cidMb


findConstants :: Knowledge -> [Expr] -> [(Expr, Expr)]
findConstants γ es = [(EVar x, c) | (x,c) <- go [] (concatMap splitPAnd es)]  
  where 
    go su ess = if ess == ess' 
                  then su 
                  else go (su ++ su') ess' 
       where ess' = subst (mkSubst su') <$> ess
             su'  = makeSu ess 
    makeSu exprs  = [(x,c) | (EEq (EVar x) c) <- exprs 
                           , isConstant (knDCs γ) c (Just x)
                           , EVar x /= c ]

makeCandidates :: Knowledge -> ICtx -> Expr -> [Expr]
makeCandidates γ ctx expr 
  = mytracepp ("\n" ++ show (length cands) ++ " New Candidates") cands
  where 
    cands = filter (\e -> isRedex γ e && not (e `S.member` icSolved ctx)) (notGuardedApps expr)

isRedex :: Knowledge -> Expr -> Bool 
isRedex γ e = isGoodApp γ e || isIte e 
  where 
    isIte EIte {} = True 
    isIte _       = False 


isGoodApp :: Knowledge -> Expr -> Bool 
isGoodApp γ e 
  | (EVar f, es) <- splitEApp e
  , Just i       <- L.lookup f (knSummary γ)
  = length es >= i
  | otherwise
  = False 
    



getCstr :: M.HashMap SubcId (SimpC a) -> SubcId -> SimpC a 
getCstr env cid = Misc.safeLookup "Instantiate.getCstr" cid env

isPleCstr :: AxiomEnv -> SubcId -> SimpC a -> Bool
isPleCstr aenv sid c = isTarget c && M.lookupDefault False sid (aenvExpand aenv) 

type EvAccum = S.HashSet (Expr, Expr)

--------------------------------------------------------------------------------
data EvalEnv = EvalEnv
  { evEnv      :: !SymEnv
  , evAccum    :: EvAccum
  }

type EvalST a = StateT EvalEnv IO a
--------------------------------------------------------------------------------


evalOne :: ConstMap -> Knowledge -> EvalEnv -> ICtx -> InstRes -> Expr -> IO EvAccum
evalOne ienv γ env ctx res e {- null (getAutoRws γ ctx) -} = do
    (e', st) <- runStateT (fastEval ienv γ ctx res e) env  
    let evAcc' = if (mytracepp ("evalOne: " ++ showpp e) e') == e then evAccum st else S.insert (e, e') (evAccum st)
    return evAcc' 

notGuardedApps :: Expr -> [Expr]
notGuardedApps = go 
  where 
    go e@(EApp e1 e2)  = [e] ++ go e1 ++ go e2
    go (PAnd es)       = concatMap go es
    go (POr es)        = concatMap go es
    go (PAtom _ e1 e2) = go e1  ++ go e2
    go (PIff e1 e2)    = go e1  ++ go e2
    go (PImp e1 e2)    = go e1  ++ go e2 
    go (EBin  _ e1 e2) = go e1  ++ go e2
    go (PNot e)        = go e
    go (ENeg e)        = go e
    go e@(EIte b _ _)  = go b ++ [e] -- ++ go e1 ++ go e2  
    go (ECoerc _ _ e)  = go e 
    go (ECst e _)      = go e 
    go (ESym _)        = []
    go (ECon _)        = []
    go (EVar _)        = []
    go (ELam _ _)      = []
    go (ETApp _ _)     = []
    go (ETAbs _ _)     = []
    go (PKVar _ _)     = []
    go (PAll _ _)      = []
    go (PExist _ _)    = []
    go (PGrad{})       = []


fastEval :: ConstMap -> Knowledge -> ICtx -> InstRes -> Expr -> EvalST Expr
fastEval ienv γ ctx res e 
    = do env  <- gets (seSort . evEnv)
         return $ mytracepp ("evaluating" ++ show e) $ interpret ienv γ ctx env res $ simplify γ ctx e

--------------------------------------------------------------------------------
-- | 'substEq' unfolds or instantiates an equation at a particular list of
--   argument values. We must also substitute the sort-variables that appear
--   as coercions. See tests/proof/ple1.fq
--------------------------------------------------------------------------------

unfoldExpr :: ConstMap -> Knowledge -> ICtx -> SEnv Sort -> InstRes -> Expr -> {-EvalST-} Expr
unfoldExpr ie γ ctx env res (EIte e0 e1 e2) = let g' = interpret' ie γ ctx env res e0 in
                                                 if g' == PTrue
                                                    then unfoldExpr ie γ ctx env res e1
                                                    else if g' == PFalse
                                                            then unfoldExpr ie γ ctx env res e2
                                                            else EIte g' e1 e2
unfoldExpr _  _ _   _   _   e               = e

substEq :: SEnv Sort -> Equation -> [Expr] -> Expr
substEq env eq es = subst su (substEqCoerce env eq es)
  where su = mkSubst $ zip (eqArgNames eq) es

substEqCoerce :: SEnv Sort -> Equation -> [Expr] -> Expr
substEqCoerce env eq es = Vis.applyCoSub coSub $ eqBody eq
  where 
    ts    = snd    <$> eqArgs eq
    sp    = panicSpan "mkCoSub"
    eTs   = sortExpr sp env <$> es
    coSub = mkCoSub env eTs ts

mkCoSub :: SEnv Sort -> [Sort] -> [Sort] -> Vis.CoSub
mkCoSub env eTs xTs = M.fromList [ (x, unite ys) | (x, ys) <- Misc.groupList xys ] 
  where
    unite ts    = Mb.fromMaybe (uError ts) (unifyTo1 senv ts)
    senv        = mkSearchEnv env
    uError ts   = panic ("mkCoSub: cannot build CoSub for " ++ showpp xys ++ " cannot unify " ++ showpp ts) 
    xys         = Misc.sortNub $ concat $ zipWith matchSorts _xTs _eTs
    (_xTs,_eTs) = (xTs, eTs)

matchSorts :: Sort -> Sort -> [(Symbol, Sort)]
matchSorts s1 s2 = go s1 s2
  where
    go (FObj x)      {-FObj-} y    = [(x, y)]
    go (FAbs _ t1)   (FAbs _ t2)   = go t1 t2
    go (FFunc s1 t1) (FFunc s2 t2) = go s1 s2 ++ go t1 t2
    go (FApp s1 t1)  (FApp s2 t2)  = go s1 s2 ++ go t1 t2
    go _             _             = []

--------------------------------------------------------------------------------

eqArgNames :: Equation -> [Symbol]
eqArgNames = map fst . eqArgs

interpret' :: ConstMap -> Knowledge -> ICtx -> SEnv Sort -> InstRes -> Expr -> Expr
interpret' ie γ ctx env res e = mytracepp ("Interpreting " ++ show e) $ interpret ie γ ctx env res e

interpret :: ConstMap -> Knowledge -> ICtx -> SEnv Sort -> InstRes -> Expr -> Expr
interpret _  _ _   _   _   e@(ESym _)       = e
interpret _  _ _   _   _   e@(ECon _)       = e
interpret ie γ ctx env res (EVar sym)
    | Just e' <- M.lookup (EVar sym) (icSimpl ctx)
    = interpret' ie γ ctx env res e'
{-
interpret ie γ ctx env res (EVar sym)      
    | Just e'' <- M.lookup (EVar sym) ie
    = interpret' ie γ ctx env res (mytrace ("found equality for sym " ++ show sym ++ " of " ++ show e'') e'')
-}
{-
    | (anfPrefix `isPrefixOfSym` sym) || (vvName `isPrefixOfSym` sym)
    , Just sr <- L.lookup sym (M.elems (beBinds (ieBEnv ie)))
    , let r = sr_reft sr
    , Just e' <- mytrace ("attempt of isSingletonE for" ++ show sym) $ isSingletonE (reftBind r) (reftPred r)
    , let e'' = unElab e' -- unApply (removeECst e')-}
{-  where
    isSingletonE v (PAtom br e0 e1)
      | isEq br = isSingEq v e0 e1 `mplus` isSingEq v e1 e0
    isSingletonE v (PIff e0 e1) =
      isSingEq v e0 e1 `mplus` isSingEq v e1 e0
    isSingletonE v (PAnd cs) =
      msum $ map (isSingletonE v) cs
    isSingletonE _ _ =
      Nothing

    isSingEq v e0 e1 = do
      guard $ EVar v == dropECst e0 && not (S.member v $ exprSymbolsSet e1)
      Just e1

    isEq r = r == Eq || r == Ueq-}
interpret _  _ _   _   _   e@(EVar _)       = e
interpret ie γ ctx env res   (EApp e1 e2)
  | isSetPred e1                         = let e2' = interpret' ie γ ctx env res e2 in 
                                             applySetFolding e1 e2'
interpret ie γ ctx env res e@(EApp _ _)     = case splitEApp e of
  (f, es) -> let (f':es') = map (interpret' ie γ ctx env res) (f:es) in interpretApp ie γ ctx env f' es'
    where
      interpretApp ie γ ctx env (EVar f) es
        | Just eq <- M.lookup f (knAms γ)
        , length (eqArgs eq) <= length es 
        = let (es1,es2) = splitAt (length (eqArgs eq)) es
              ges       = substEq env eq es1
              exp       = unfoldExpr ie γ ctx env res ges 
              exp'      = eApps exp es2 in  --exp' -- TODO undo
            if (eApps (EVar f) es) == exp' then exp' else interpret' ie γ ctx env res exp'

      interpretApp ie γ ctx env (EVar f) (e1:es)
        | (EVar dc, as) <- splitEApp e1
        , Just rw <- M.lookup (f, dc) (knSims γ)
        , length as == length (smArgs rw)
        = let e' = eApps (subst (mkSubst $ zip (smArgs rw) as) (smBody rw)) es in --e' -- TODO undo
            if (eApps (EVar f) es) == e' then e' else interpret' ie γ ctx env res e' 

      interpretApp _  γ _   _   (EVar f) ([e0])
        | (EVar dc, _as) <- splitEApp e0
        , isTestSymbol f
        = if testSymbol dc == f then PTrue else 
            if S.member dc (knAllDCs γ) then PFalse else {-simplify γ ctx $-} eApps (EVar f) [e0]

      interpretApp _  _ _   _   f        es     = {-simplify γ ctx $-} eApps f es
interpret ie γ ctx env res   (ENeg e1)      = let e1' = interpret' ie γ ctx env res e1 in
                                                applyConstantFolding Minus (ECon (I 0)) e1'
--                                             simplify γ ctx (ENeg e1')
interpret ie γ ctx env res   (EBin o e1 e2) = let e1' = interpret' ie γ ctx env res e1 
                                                  e2' = interpret' ie γ ctx env res e2 in
                                                applyConstantFolding o e1' e2'
--                                             simplify γ ctx (EBin o e1' e2')
interpret ie γ ctx env res   (EIte g e1 e2) = let b = interpret' ie γ ctx env res g in
                                                if b == PTrue then interpret' ie γ ctx env res e1 else
                                                  if b == PFalse then interpret' ie γ ctx env res e2 else 
                                                    simplify γ ctx $ EIte b e1 e2
--                                             EIte b (interpret' γ ctx env e1) (interpret' γ ctx env e2)
interpret ie γ ctx env res   (ECst e1 s)    = let e1' = interpret' ie γ ctx env res e1 in
                                                simplifyCasts e1' s -- ECst e1' s
interpret ie γ ctx env res (ELam (x,s) e)   = let γ' = γ { knLams = (x, s) : knLams γ }
                                                  e' = interpret' ie γ' ctx env res e in 
                                                ELam (x, s) e'
interpret ie γ ctx env res   (ETApp e1 t)   = let e1' = interpret' ie γ ctx env res e1 in ETApp e1' t
interpret ie γ ctx env res   (ETAbs e1 sy)  = let e1' = interpret' ie γ ctx env res e1 in ETAbs e1' sy
interpret ie γ ctx env res   (PAnd es)      = let es' = map (interpret' ie γ ctx env res) es in go [] (reverse es')
  where
    go []  []     = PTrue
    go [p] []     = interpret' ie γ ctx env res p
    go acc []     = PAnd acc
    go acc (e:es) = if e == PTrue then go acc es
                                  else if e == PFalse then PFalse else go (e:acc) es
interpret ie γ ctx env res (POr es)         = let es' = map (interpret' ie γ ctx env res) es in go [] (reverse es')
  where
    go []  []     = PFalse
    go [p] []     = interpret' ie γ ctx env res p
    go acc []     = POr acc
    go acc (e:es) = if e == PTrue then PTrue
                                  else if e == PFalse then go acc es else go (e:acc) es
interpret ie γ ctx env res (PNot e)         = let e' = interpret' ie γ ctx env res e in case e' of
    (PNot e'')    -> e''
    PTrue         -> PFalse 
    PFalse        -> PTrue 
    _             -> PNot e'
interpret ie γ ctx env res (PImp e1 e2)     = let e1' = interpret' ie γ ctx env res e1 
                                                  e2' = interpret' ie γ ctx env res e2 in
                                                if e1' == PFalse || e2' == PTrue then PTrue else
                                                  if e1' == PTrue then e2' else
                                                    if e2' == PFalse then interpret' ie γ ctx env res (PNot e1') else 
                                                      PImp e1' e2'
interpret ie γ ctx env res (PIff e1 e2)     = let e1' = interpret' ie γ ctx env res e1 
                                                  e2' = interpret' ie γ ctx env res e2 in
                                                if e1' == PTrue then e2' else
                                                  if e2' == PTrue then e1' else
                                                    if e1' == PFalse then interpret' ie γ ctx env res (PNot e2') else
                                                      if e2' == PFalse then interpret' ie γ ctx env res (PNot e1') else
                                                        PIff e1' e2'
interpret ie γ ctx env res (PAtom o e1 e2)  = let e1' = interpret' ie γ ctx env res e1
                                                  e2' = interpret' ie γ ctx env res e2 in
                                                applyBooleanFolding o e1' e2'
interpret _  _ _   _   _   e@(PKVar _ _)    = e
interpret ie γ ctx env res e@(PAll xss e1)  = case xss of
  [] -> interpret' ie γ ctx env res e1
  _  -> e
interpret ie γ ctx env res e@(PExist xss e1) = case xss of
  [] -> interpret' ie γ ctx env res e1
  _  -> e
interpret _  _ _   _   _   e@(PGrad _ _ _ _) = e
interpret ie γ ctx env res (ECoerc s t e)    = let e' = interpret' ie γ ctx env res e in
                                                 if s == t then e' else (ECoerc s t e')

        
--------------------------------------------------------------------------------
-- | Knowledge (SMT Interaction)
--------------------------------------------------------------------------------
data Knowledge = KN 
  { knSims              :: M.HashMap (Symbol, Symbol) Rewrite  -- ^ Rewrite rules came from match and data type definitions 
  , knAms               :: M.HashMap Symbol Equation  -- ^ All function definitions -- restore ! here?
  , knLams              :: ![(Symbol, Sort)]
  , knSummary           :: ![(Symbol, Int)]     -- ^ summary of functions to be evaluates (knSims and knAsms) with their arity
  , knDCs               :: !(S.HashSet Symbol)  -- ^ data constructors drawn from Rewrite 
  , knAllDCs            :: !(S.HashSet Symbol)  -- ^ 
  , knSels              :: !SelectorMap 
  , knConsts            :: !ConstDCMap
  , knAutoRWs           :: M.HashMap SubcId [AutoRewrite]
  , knRWTerminationOpts :: RWTerminationOpts
  }

knowledge :: Config -> SInfo a -> Knowledge
knowledge cfg si = KN 
  { knSims                     = M.fromList $ (\r -> ((smName r, smDC r), r)) <$> sims 
  , knAms                      = M.fromList $ (\a -> (eqName a, a)) <$> aenvEqs aenv
  , knLams                     = [] 
  , knSummary                  =    ((\s -> (smName s, 1)) <$> sims) 
                                 ++ ((\s -> (eqName s, length (eqArgs s))) <$> aenvEqs aenv)
  , knDCs                      = S.fromList (smDC <$> sims)  <> constNames si
  , knAllDCs                   = S.fromList $ (val . dcName) <$> concatMap ddCtors (ddecls si)
  , knSels                     = M.fromList . Mb.catMaybes $ map makeSel  sims 
  , knConsts                   = M.fromList . Mb.catMaybes $ map makeCons sims 
  , knAutoRWs                  = aenvAutoRW aenv
  , knRWTerminationOpts        = if (rwTerminationCheck cfg)
                                   then RWTerminationCheckEnabled 
                                   else RWTerminationCheckDisabled
  } 
  where 
    sims = aenvSimpl aenv ++ concatMap reWriteDDecl (ddecls si) -- store as list too? 
    aenv = ae si 

    makeCons rw 
      | null (syms $ smBody rw)
      = Just (smName rw, (smDC rw, smBody rw))
      | otherwise
      = Nothing 

    makeSel rw 
      | EVar x <- smBody rw
      = (smName rw,) . (smDC rw,) <$> L.elemIndex x (smArgs rw)
      | otherwise 
      = Nothing 

    constNames si = (S.fromList . fst . unzip . toListSEnv . gLits $ si) `S.union`
                      (S.fromList . fst . unzip . toListSEnv . dLits $ si)
-- testSymbol (from names)


reWriteDDecl :: DataDecl -> [Rewrite]
reWriteDDecl ddecl = concatMap go (ddCtors ddecl) 
  where 
    go (DCtor f xs) = zipWith (\r i -> SMeasure r f' ys (EVar (ys!!i)) ) rs [0..]
       where 
        f'  = symbol f 
        rs  = (val . dfName) <$> xs  
        mkArg ws = zipWith (\_ i -> intSymbol (symbol ("darg"::String)) i) ws [0..]
        ys  = mkArg xs 

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- (sel_i, D, i), meaning sel_i (D x1 .. xn) = xi, 
-- i.e., sel_i selects the ith value for the data constructor D  
type SelectorMap = M.HashMap Symbol (Symbol, Int)
type ConstDCMap  = M.HashMap Symbol (Symbol, Expr)

-- ValueMap maps expressions to constants (including data constructors)
type ConstMap = M.HashMap Expr Expr
type LDataCon = Symbol              -- Data Constructors 

isSimplification :: S.HashSet LDataCon -> (Expr,Expr) -> Bool 
isSimplification dcs (_,c) = isConstant dcs c Nothing
  

isConstant :: S.HashSet LDataCon -> Expr -> Maybe Symbol -> Bool 
isConstant dcs e sym = mytrace ("for expression " ++ show e ++ " maybe symbol " ++ show sym ++ "difference is " ++ show (S.difference (S.fromList $ syms e) dcs)) S.null (S.difference (S.fromList $ syms e) dcs) 

class Simplifiable a where 
  simplify :: Knowledge -> ICtx -> a -> a 


instance Simplifiable Expr where 
  simplify γ ictx e = mytracepp ("simplification of " ++ show e) $ fix (Vis.mapExpr tx) e 
    where 
      fix f e = if e == e' then e else fix f e' where e' = f e 
      tx e 
        | Just e' <- M.lookup e (icSimpl ictx)
        = e' 
      tx (EBin bop e1 e2) = applyConstantFolding bop e1 e2
      tx (ENeg e)         = applyConstantFolding Minus (ECon (I 0)) e
      tx (EApp e1 e2)
        | isSetPred e1    = applySetFolding e1 e2
      tx (EApp (EVar f) a)
        | Just (dc, c)  <- M.lookup f (knConsts γ) 
        , (EVar dc', _) <- splitEApp a
        , dc == dc' 
        = c
      tx (EIte b e1 e2)
        | isTautoPred b  = e1 
        | isContraPred b = e2
      tx (ECst e s)       = simplifyCasts e s
      tx (ECoerc s t e)
        | s == t = e 
      tx (EApp (EVar f) a)
        | Just (dc, i)  <- M.lookup f (knSels γ) 
        , (EVar dc', es) <- splitEApp a
        , dc == dc' 
        = es!!i
      tx (PAnd es)         = go [] (reverse es)
        where
          go []  []     = PTrue
          go [p] []     = p
          go acc []     = PAnd acc
          go acc (e:es) = if e == PTrue then go acc es
                                  else if e == PFalse then PFalse else go (e:acc) es
      tx (POr es)          = go [] (reverse es)
        where
          go []  []     = PFalse
          go [p] []     = p
          go acc []     = POr acc
          go acc (e:es) = if e == PTrue then PTrue
                                  else if e == PFalse then go acc es else go (e:acc) es
      tx (PNot e)          = if e == PTrue then PFalse 
                                else if e == PFalse then PTrue 
                                else PNot e
      tx (PAtom rel e1 e2) = applyBooleanFolding rel e1 e2
      tx e = e
      
applyBooleanFolding :: Brel -> Expr -> Expr -> Expr
applyBooleanFolding brel e1 e2 = 
  case (e1, e2) of 
    ((ECon (R left)), (ECon (R right))) ->
      Mb.fromMaybe e (bfR brel left right)
    ((ECon (R left)), (ECon (I right))) ->
      Mb.fromMaybe e (bfR brel left (fromIntegral right))
    ((ECon (I left)), (ECon (R right))) ->
      Mb.fromMaybe e (bfR brel (fromIntegral left) right)
    ((ECon (I left)), (ECon (I right))) ->
      Mb.fromMaybe e (bfI brel left right)
    _ -> if isTautoPred e then PTrue else 
           if isContraPred e then PFalse else e
  where
    e = PAtom brel e1 e2
    
    getOp :: Ord a => Brel -> (a -> a -> Bool)
    getOp Gt   =  (>)
    getOp Ge   =  (>=)
    getOp Lt   =  (<)
    getOp Le   =  (<=)
    getOp Eq   =  (==)
    getOp Ne   =  (/=)
    getOp Ueq  =  (==)
    getOp Une  =  (/=)

    bfR :: Brel -> Double -> Double -> Maybe Expr
    bfR brel left right = if (getOp brel) left right then Just PTrue else Just PFalse

    bfI :: Brel -> Integer -> Integer -> Maybe Expr
    bfI brel left right = if (getOp brel) left right then Just PTrue else Just PFalse
        

applyConstantFolding :: Bop -> Expr -> Expr -> Expr
applyConstantFolding bop e1 e2 =
  case (e1, e2) of
    ((ECon (R left)), (ECon (R right))) ->
      Mb.fromMaybe e (cfR bop left right)
    ((ECon (R left)), (ECon (I right))) ->
      Mb.fromMaybe e (cfR bop left (fromIntegral right))
    ((ECon (I left)), (ECon (R right))) ->
      Mb.fromMaybe e (cfR bop (fromIntegral left) right)
    ((ECon (I left)), (ECon (I right))) ->
      Mb.fromMaybe e (cfI bop left right)
    (EBin Mod  _   _              , _)  -> e
    (EBin bop1 e11 (ECon (R left)), ECon (R right))
      | bop == bop1 -> Mb.fromMaybe e ((EBin bop e11) <$> (cfR (rop bop) left right))
      | otherwise   -> e
    (EBin bop1 e11 (ECon (R left)), ECon (I right))
      | bop == bop1 -> Mb.fromMaybe e ((EBin bop e11) <$> (cfR (rop bop) left (fromIntegral right)))
      | otherwise   -> e
    (EBin bop1 e11 (ECon (I left)), ECon (R right))
      | bop == bop1 -> Mb.fromMaybe e ((EBin bop e11) <$> (cfR (rop bop) (fromIntegral left) right))
      | otherwise   -> e
    (EBin bop1 e11 (ECon (I left)), ECon (I right))
      | bop == bop1 -> Mb.fromMaybe e ((EBin bop e11) <$> (cfI (rop bop) left right))
      | otherwise   -> e
    _ -> e
  where
    
    rop :: Bop -> Bop
    rop Plus   = Plus
    rop Minus  = Plus
    rop Times  = Times
    rop Div    = Times
    rop RTimes = RTimes
    rop RDiv   = RTimes
    rop Mod    = Mod

    e = EBin bop e1 e2
    
    getOp :: Num a => Bop -> Maybe (a -> a -> a)
    getOp Minus    = Just (-)
    getOp Plus     = Just (+)
    getOp Times    = Just (*)
    getOp RTimes   = Just (*)
    getOp _        = Nothing

    cfR :: Bop -> Double -> Double -> Maybe Expr
    cfR bop left right = fmap go (getOp' bop)
      where
        go f = ECon $ R $ f left right
        
        getOp' Div      = Just (/)
        getOp' RDiv     = Just (/)
        getOp' op       = getOp op

    cfI :: Bop -> Integer -> Integer -> Maybe Expr
    cfI bop left right = fmap go (getOp' bop)
      where
        go f = ECon $ I $ f left right
        
        getOp' Mod = Just mod
        getOp' op  = getOp op

isSetPred :: Expr -> Bool
isSetPred (EVar s) | s == setEmp          = True
isSetPred (EApp e1 _) = case e1 of
  (EVar s) | s == setMem || s == setSub  -> True
  _                                      -> False
isSetPred _                               = False

-- Note: this is currently limited to sets of integer constants
applySetFolding :: Expr -> Expr -> Expr
applySetFolding e1 e2   = case e1 of
    (EVar s) | s == setEmp
      -> Mb.fromMaybe e $ pure (fromBool . S.null)   <*> evalSetI e2
    (EApp (EVar s) e1') | s == setMem
      -> Mb.fromMaybe e $ fromBool <$> (S.member <$> getInt e1' <*> evalSetI e2)
                        | s == setEmp
      -> Mb.fromMaybe e $ fromBool <$> (S.null <$> (S.difference <$> evalSetI e1' <*> evalSetI e2))
                        | otherwise 
      -> e
    _                   -> e
  where
    e = EApp e1 e2

    fromBool True  = PTrue
    fromBool False = PFalse

    getInt :: Expr -> Maybe Integer
    getInt (ECon (I n)) = Just n
    getInt _            = Nothing
    
    getOp :: (Eq a, Hashable a) => Symbol -> Maybe (S.HashSet a -> S.HashSet a -> S.HashSet a)
    getOp s | s == setCup = Just S.union
            | s == setCap = Just S.intersection
            | s == setDif = Just S.difference
            | otherwise   = Nothing

    evalSetI :: Expr -> Maybe (S.HashSet Integer)
    evalSetI (EApp e1 e2) = case e1 of
      (EVar s) | s == setEmpty -> Just S.empty
               | s == setSng   -> case e2 of
        (ECon (I n))             -> Just $ S.singleton n
        _                        -> Nothing
      (EApp (EVar f) e1')  -> getOp f <*> evalSetI e1' <*> evalSetI e2
      _                    -> Nothing   
    evalSetI _            = Nothing

simplifyCasts :: Expr -> Sort -> Expr
simplifyCasts (ECon (I n)) FInt  = ECon (I n)
simplifyCasts (ECon (R x)) FReal = ECon (R x)
simplifyCasts e            s     = ECst e s

-------------------------------------------------------------------------------
-- | Normalization of Equation: make their arguments unique -------------------
-------------------------------------------------------------------------------

class Normalizable a where 
  normalize :: a -> a 

instance Normalizable (GInfo c a) where 
  normalize si = si {ae = normalize $ ae si}

instance Normalizable AxiomEnv where 
  normalize aenv = aenv { aenvEqs   = {-notracepp-} mytracepp "aenvEqs"   (normalize <$> aenvEqs   aenv)
                        , aenvSimpl = {-notracepp-} mytracepp "aenvSimpl" (normalize <$> aenvSimpl aenv) }

instance Normalizable Rewrite where 
  normalize rw = rw { smArgs = xs', smBody = normalizeBody (smName rw) $ subst su $ smBody rw }
    where 
      su  = mkSubst $ zipWith (\x y -> (x,EVar y)) xs xs'
      xs  = smArgs rw 
      xs' = zipWith mkSymbol xs [0..]
      mkSymbol x i = x `suffixSymbol` intSymbol (smName rw) i 

instance Normalizable Equation where 
  normalize eq = eq {eqArgs = zip xs' ss, 
                     eqBody = normalizeBody (eqName eq) $ subst su $ eqBody eq }
    where 
      su           = mkSubst $ zipWith (\x y -> (x,EVar y)) xs xs'
      (xs,ss)      = unzip (eqArgs eq) 
      xs'          = zipWith mkSymbol xs [0..]
      mkSymbol x i = x `suffixSymbol` intSymbol (eqName eq) i 

normalizeBody :: Symbol -> Expr -> Expr
normalizeBody f = go   
  where 
    go e 
      | any (== f) (syms e) 
      = go' e 
    go e 
      = e 
    
    go' (PAnd [PImp c e1,PImp (PNot c') e2])
      | c == c' = EIte c e1 (go' e2)
    go' e = e 

_splitBranches :: Symbol -> Expr -> [(Expr, Expr)]
_splitBranches f = go   
  where 
    go (PAnd es) 
      | any (== f) (syms es) 
      = go' <$> es
    go e 
      = [(PTrue, e)]

    go' (PImp c e) = (c, e) 
    go' e          = (PTrue, e)
