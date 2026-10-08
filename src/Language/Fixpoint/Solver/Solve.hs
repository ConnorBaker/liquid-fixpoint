{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

--------------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ---------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.Solve (solve) where

import           Control.Monad (forM, when, filterM, foldM)
import           Control.Monad.Reader
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Misc            as Misc
import qualified Language.Fixpoint.Types           as F
import qualified Language.Fixpoint.Types.Solutions as Sol
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Config hiding (stats)
import           Language.Fixpoint.SortCheck          (ElabParam(..), elaborate, unApply, unElab)
import           Language.Fixpoint.Solver.Sanitize (symbolEnv)
import qualified Language.Fixpoint.Solver.Solution  as S
import qualified Language.Fixpoint.Smt.Types as T
import qualified Language.Fixpoint.Solver.Worklist  as W
import qualified Language.Fixpoint.Solver.Eliminate as E
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Graph
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
import           Language.Fixpoint.Verbosity
import           Control.DeepSeq
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
-- import qualified Data.Maybe          as Mb
import qualified Data.List           as L
import Language.Fixpoint.Types (resStatus, FixResult(Unsafe))
import Language.Fixpoint.Smt.Interface (smtComment)
import qualified Language.Fixpoint.Types.Errors as Errors
import Language.Fixpoint.Solver.Interpreter (instInterpreter)
import qualified Language.Fixpoint.Solver.PLE as PLE      (instantiate)

mytrace :: String -> a -> a
mytrace
  -- s x = trace s x
  _ x = x
{-
solve_ :: (NFData a, F.Fixpoint a, F.Loc a)
       => Config
       -> F.SInfo a
       -> Sol.Solution
       -> W.Worklist a
       -> SolveM a (F.Result (Integer, a), Stats)
       -}
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
solve ::
    forall a.
    (NFData a, F.Fixpoint a, Show a, F.Loc a) =>
    Config -> F.SInfo a -> ElabParam -> S.HashSet F.Symbol -> F.SourceScopes -> F.SInfo a -> IO (F.Result (Integer, a))
--------------------------------------------------------------------------------

solve cfg source elabParam scope sourceScopes fi = do
    whenLoud $ donePhase Misc.Loud "Worklist Initialize"
    vb <- getVerbosity
    (res, stat) <- (if Quiet == vb then id else withProgressFI sI) $ runSolverM cfg sI elabParam act
    when (solverStats cfg) $ printStats fi wkl stat
    -- print (numIter stat)
    return res
  where
    act :: SolveM a (F.Result (Integer, a), Stats)
    act = do
        ctx <- getContext
        let sEnv = symbolEnv cfg fi
            elaborateQualifier = elaborate (ElabParam (T.ctxElabF ctx) (F.atLoc F.dummySpan "solve") sEnv)
            s1 = s0{Sol.sMap = M.map (elabQBind elaborateQualifier) (Sol.sMap s0)}
        (result, statistics) <- solve_ cfg source scope sourceScopes fi s1 wkl
        pure (tidyResult cfg (F.seSort sEnv) result, statistics)
    -- solverInfo computes the set of cut and non-cut kvars, then initializes
    -- the solutions of the non-cut KVars (in the sHyp field)
    --
    -- S.init provides an initial solution for the cut KVars
    sI = solverInfo cfg fi
    wkl = W.init sI
    s0 = (siSol sI){Sol.sMap = S.init cfg fi ks}
    ks = siVars sI
    elabQBind elaborateQualifier (Sol.QB xs) = Sol.QB (map elabEQual xs)
      where
        elabEQual eq = eq{Sol.eqPred = elaborateQualifier (Sol.eqPred eq)}

--------------------------------------------------------------------------------
-- | Progress Bar
--------------------------------------------------------------------------------
withProgressFI :: SolverInfo a -> IO b -> IO b
withProgressFI = withProgress . (+ 1) . fromIntegral . cNumScc . siDeps
--------------------------------------------------------------------------------

printStats :: F.SInfo a ->  W.Worklist a -> Stats -> IO ()
printStats fi w s = putStrLn "\n" >> ppTs [ ptable fi, ptable s, ptable w ]
  where
    ppTs          = putStrLn . showpp . mconcat

--------------------------------------------------------------------------------
solverInfo :: Config -> F.SInfo a -> SolverInfo a
--------------------------------------------------------------------------------
solverInfo cfg fI
  | useElim cfg = E.solverInfo cfg fI
  | otherwise   = SI mempty fI cD (siKvars fI)
  where
    cD          = elimDeps fI (kvEdges fI) mempty

siKvars :: F.SInfo a -> S.HashSet F.KVar
siKvars = S.fromList . M.keys . F.ws

doInterpret :: (F.Loc a) =>  Config -> F.SInfo a -> [F.SubcId] -> SolveM a (F.BindEnv a)
doInterpret cfg fi subcIds = liftIO $ instInterpreter cfg fi (Just subcIds)

--------------------------------------------------------------------------------
{-# SCC solve_ #-}
solve_ :: (NFData a, F.Fixpoint a, F.Loc a)
       => Config
       -> F.SInfo a
       -> S.HashSet F.Symbol
       -> F.SourceScopes
       -> F.SInfo a
       -> Sol.Solution
       -> W.Worklist a
       -> SolveM a (F.Result (Integer, a), Stats)
--------------------------------------------------------------------------------
solve_ cfg source scope sourceScopes fi s2 wkl = do
  liftSMT $ smtComment "solve: start"
  (s3, res0) <- sendConcreteBindingsToSMT F.emptyIBindEnv (F.bs fi) $ \bindingsInSmt -> do
    -- let s3   = solveEbinds fi s2
    s3       <- {- SCC "sol-refine" -} refine scope bindingsInSmt fi s2 wkl
    res0     <- {- SCC "sol-result" -} result scope bindingsInSmt cfg sourceScopes fi (W.unsatCandidates wkl) s3
    return (s3, res0)

  (fi1, res1) <- case resStatus res0 of  {- first run the interpreter -}
    Unsafe _ bads | rewriteAxioms cfg && interpreter cfg && F.aenvNative (F.ae fi) == Nothing -> do
      liftSMT $ smtComment "solve: interpreter"
      bs <- doInterpret cfg fi (map fst $ mytrace ("before the Interpreter " ++ show (length bads) ++ " constraints remain") bads)
      let fi1 = fi { F.bs = bs }
          badCs = lookupCMap (F.cm fi) <$> map fst bads
      liftSMT $ smtComment "solve: pos-interpreter check"
      fmap (fi1,) $ sendConcreteBindingsToSMT F.emptyIBindEnv bs $ \bindingsInSmt ->
        result scope bindingsInSmt cfg sourceScopes fi1 badCs s3
    _ -> return  (fi, mytrace "all checked before interpreter" res0)

  res2  <- case resStatus res1 of  {- then run normal PLE on remaining unsolved constraints -}
    Unsafe _ bads2 | rewriteAxioms cfg -> do
      when (save cfg) $
        liftIO $ S.saveSolution cfg ".pre-ple" res1
      liftSMT $ smtComment "solve: ple"
      bs <- liftSMT $ PLE.instantiate cfg source scope fi1 (Just s3) (Just $ map fst bads2)
      -- Check the constraints one last time after PLE
      let fi2 = fi { F.bs = bs }
          badsCs2 = lookupCMap (F.cm fi) <$> map fst bads2
      liftSMT $ smtComment "solve: pos-ple check"
      sendConcreteBindingsToSMT F.emptyIBindEnv bs $ \bindingsInSmt ->
        result scope bindingsInSmt cfg sourceScopes fi2 badsCs2 s3
    _ -> return $ mytrace "all checked with interpreter" res1

  liftSMT $ smtComment "solve: finished"
  st      <- stats
  return $!! (res2, st)


--------------------------------------------------------------------------------
{- | Project solutions in their canonical typed scope before choosing whether
to retain casts. Presentation preserves the predicate's binding identities.
-}

--------------------------------------------------------------------------------
tidyResult :: Config -> F.SEnv F.Sort -> F.Result a -> F.Result a
tidyResult cfg declarations r =
    r
        { F.resSolution = M.mapWithKey project (F.resSolution r)
        , F.resNonCutsSolution = M.mapWithKey (\k -> fmap (project k)) (F.resNonCutsSolution r)
        }
  where
    project k = present . S.simplifyKVar declarations (F.fromListSEnv [(F.formalCanonical f, F.formalSort f) | f <- M.lookupDefault [] k (F.resScopes r)]) . unApply
    present = if sortedSolution cfg then id else unElab

--------------------------------------------------------------------------------
{-# SCC refine #-}
-- | Implementation of the inference algorithm from:
--
-- "Liquid Types", PLDI 2008, https://ranjitjhala.github.io/static/liquid_types.pdf
--
refine
  :: forall a. F.Loc a
  => S.HashSet F.Symbol
  -> F.IBindEnv
  -> F.SInfo a
  -> Sol.Solution
  -> W.Worklist a
  -> SolveM a Sol.Solution
--------------------------------------------------------------------------------
refine scope bindingsInSmt info s0 w0 = do
  let initial = S.prepareSummaryState scope info
  go initial s0 w0
 where
  go :: S.SummaryState -> Sol.Solution -> W.Worklist a -> SolveM a Sol.Solution
  go initial s w
    | Just (c, w', newScc, rnk) <- W.pop w = do
        i <- tickIter newScc
        (b, s') <- refineC initial scope bindingsInSmt info i s c
        lift $ writeLoud $ refineMsg i c b rnk (showpp s')
        let w'' = if b then W.push c w' else w'
        go initial s' w''
    | otherwise = return s
   where
    -- DEBUG
    refineMsg i c b rnk s =
      printf
        "\niter=%d id=%d change=%s rank=%d s=%s\n"
        i
        (F.subcId c)
        (show b)
        rnk
        s

---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
{-# SCC refineC #-}
refineC ::
    forall a.
    (F.Loc a) =>
    S.SummaryState ->
    S.HashSet F.Symbol ->
    F.IBindEnv ->
    F.SInfo a ->
    Int ->
    Sol.Solution ->
    F.SimpC a ->
    SolveM a (Bool, Sol.Solution)
---------------------------------------------------------------------------
refineC initial scope bindingsInSmt info _i s c =
    do
        context <- getContext
        let cfg = T.config context
        let krhs = rhsCands cfg s
        if all (null . snd) krhs
            then return (False, s)
            else do
                let (definitions, lhs) = S.lhsPredShared cfg initial scope bindingsInSmt info s c
                kqs <- forM krhs $ \(k, rhs) ->
                    (,) k . Sol.QB <$> filterValid (cstrSpan c) definitions lhs rhs
                return $ S.update s kqs
  where
    rhsCands :: Config -> Sol.Solution -> [(F.KVar, Sol.Cand Sol.EQual)]
    rhsCands cfg s = map cnd $ M.toList occurrences
      where
        env = S.combinedEnv (Just $ F.subcId c) info scope (F.senv c) (F.srcSpan c) F.emptyIBindEnv mempty
        ks = predKs . F.crhs $ c
        occurrences = M.fromListWith (++) [(k, [(su, tvsu)]) | (k, su, tvsu) <- ks]
        -- A retained qualifier must hold at every occurrence of its KVar.
        -- Group actuals, not already-instantiated parallel qualifier lists.
        cnd :: (F.KVar, [(F.Subst, F.TyVarSubst)]) -> (F.KVar, Sol.Cand Sol.EQual)
        cnd (k, reversedActuals) =
            ( k
            , [ ( F.PAnd [S.applyExpr cfg env s p | (su, tvsu) <- actuals, (p, _) <- S.qbPreds su tvsu (Sol.QB [q])]
                , q
                )
              | q <- qualifiers
              ]
            )
          where
            actuals = reverse reversedActuals
            Sol.QB qualifiers = Sol.lookupQBind s k

predKs :: F.Expr -> [(F.KVar, F.Subst, F.TyVarSubst)]
predKs (F.PAnd ps)    = concatMap predKs ps
predKs (F.PKVar k tvsu su) = [(k, F.substFromKSubst su, tvsu)]
predKs _              = []

--------------------------------------------------------------------------------
-- | Convert Solution into Result ----------------------------------------------
--------------------------------------------------------------------------------
{-# SCC result #-}
result
  :: (F.Fixpoint a, F.Loc a, NFData a)
  => S.HashSet F.Symbol
  -> F.IBindEnv
  -> Config
  -> F.SourceScopes
  -> F.SInfo a
  -> [F.SimpC a]
  -> Sol.Solution
  -> SolveM a (F.Result (Integer, a))
--------------------------------------------------------------------------------
result scope bindingsInSmt cfg sourceScopes fi cs s =
  sendConcreteBindingsToSMT bindingsInSmt be $ \bindingsInSmt2 -> do
    lift       $ writeLoud "Computing Result"
    stat      <- result_ scope bindingsInSmt2 fi cfg cs s
    lift       $ whenLoud $ putStrLn $ "RESULT: " ++ show (F.sid <$> stat)
    resCut    <- solResult cfg s
    let resNonCut = S.nonCutsResult cfg scope fi s
        scopes = either (Errors.die . Errors.err F.dummySpan . text) id $ resultScopes sourceScopes fi (M.keys resCut ++ M.keys resNonCut) be
    return     $ F.Result (ci <$> stat) resCut resNonCut scopes
  where
    ci c = (F.subcId c, F.sinfo c)
    be = F.bs fi

resultScopes :: F.SourceScopes -> F.SInfo a -> [F.KVar] -> F.BindEnv a -> Either String F.ResultScopes
resultScopes sources fi ks be = M.fromList <$> traverse scope ks
  where
    binders = M.fromList (F.bindEnvToList be)
    scope k = do
      w <- maybe (Left "result KVar has no WF") Right (M.lookup k (F.ws fi))
      names <- maybe (Left "result KVar has no source scope") Right (M.lookup k sources)
      let (value, valueSort, _) = F.wrft w
      bindings <- traverse (binding names) (L.sort $ F.elemsIBindEnv $ F.wenv w)
      valueFormal <- formal names value valueSort
      normalized <- foldM insertFormal [] (valueFormal : bindings)
      if S.fromList (map F.formalCanonical normalized) == M.keysSet names
        then Right (k, reverse normalized)
        else Left "source scope does not match result WF domain"
    binding names i = do
      (symbol, sr, _) <- maybe (Left "result WF binder is missing") Right (M.lookup i binders)
      formal names symbol (F.sr_sort sr)
    formal names canonical sort = do
      source <- maybe (Left "result formal lacks a source") Right (M.lookup canonical names)
      Right (F.Formal source canonical sort)
    insertFormal seen candidate =
      case L.find ((== F.formalCanonical candidate) . F.formalCanonical) seen of
        Nothing -> Right (candidate : seen)
        Just previous
          | previous == candidate -> Right seen
          | otherwise -> Left "result canonical formal has conflicting source or sort"

solResult :: Config -> Sol.Solution -> SolveM ann (M.HashMap F.KVar F.Expr)
solResult cfg = minimizeResult cfg . Sol.result

result_
  :: (F.Loc a, NFData a)
  => S.HashSet F.Symbol
  -> F.IBindEnv
  -> F.SInfo a
  -> Config
  -> [F.SimpC a]
  -> Sol.Solution
  -> SolveM a (F.FixResult (F.SimpC a))
result_ scope bindingsInSmt info cfg cs0 s = do
  let initial = S.prepareSummaryState scope info
  unsatisfiedConstraints <- filterM (isUnsat initial scope bindingsInSmt info s) cs
  sts <- stats
  pure $ res sts unsatisfiedConstraints
  where
    cs = isChecked cfg cs0
    res sts [] = F.Safe sts
    res sts cs' = F.Unsafe sts cs'

isChecked :: Config -> [F.SimpC a] -> [F.SimpC a]
isChecked cfg cs = case checkCstr cfg of
  []   -> cs
  ids  -> let s = S.fromList ids in
          [c | c <- cs, S.member (F.subcId c) s ]

--------------------------------------------------------------------------------
-- | `minimizeResult` transforms each KVar's result by removing
--   conjuncts that are implied by others. That is,
--
--      minimizeConjuncts :: ps:[Pred] -> {qs:[Pred] | subset qs ps}
--
--   such that `minimizeConjuncts ps` is a minimal subset of ps where no
--   is implied by /\_{q' in qs \ qs}
--   see: tests/pos/min00.fq for an example.
--------------------------------------------------------------------------------
minimizeResult :: Config -> M.HashMap F.KVar F.Expr
               -> SolveM ann (M.HashMap F.KVar F.Expr)
--------------------------------------------------------------------------------
minimizeResult cfg s
  | minimalSol cfg = mapM minimizeConjuncts s
  | otherwise      = return s

minimizeConjuncts :: F.Expr -> SolveM ann F.Expr
minimizeConjuncts p = F.pAnd <$> go (F.conjuncts p) []
  where
    go []     acc   = return acc
    go (p:ps) acc   = do b <- isValid F.dummySpan (F.pAnd (acc ++ ps)) p
                         if b then go ps acc
                              else go ps (p:acc)

--------------------------------------------------------------------------------
isUnsat ::
    (F.Loc a, NFData a) => S.SummaryState -> S.HashSet F.Symbol -> F.IBindEnv -> F.SInfo a -> Sol.Solution -> F.SimpC a -> SolveM a Bool
--------------------------------------------------------------------------------
isUnsat initial scope bindingsInSmt info s c = do
    -- lift   $ printf "isUnsat %s" (show (F.subcId c))
    _ <- tickIter True -- newScc
    context <- getContext
    let cfg = T.config context
        (definitions, lp) = S.lhsPredShared cfg initial scope bindingsInSmt info s c
        rp = rhsPred c
    res <- null <$> filterValid (cstrSpan c) definitions lp [(rp, ())]
    lift $ whenLoud $ showUnsat res (F.subcId c) lp rp
    return res

showUnsat :: Bool -> Integer -> F.Pred -> F.Pred -> IO ()
showUnsat u i lP rP = {- when u $ -} do
  putStrLn $ printf   "UNSAT id %s %s" (show i) (show u)
  putStrLn $ showpp $ "LHS:" <+> pprint lP
  putStrLn $ showpp $ "RHS:" <+> pprint rP

--------------------------------------------------------------------------------
-- | Predicate corresponding to RHS of constraint in current solution
--------------------------------------------------------------------------------
rhsPred :: F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
rhsPred c
  | isTarget c = F.crhs c
  | otherwise  = errorstar $ "rhsPred on non-target: " ++ show (F.sid c)

--------------------------------------------------------------------------------
isValid :: F.SrcSpan -> F.Expr -> F.Expr -> SolveM ann Bool
--------------------------------------------------------------------------------
isValid sp p q = not . null <$> filterValid sp [] p [(q, ())]

cstrSpan :: (F.Loc a) => F.SimpC a -> F.SrcSpan
cstrSpan = F.srcSpan . F.sinfo

{-
---------------------------------------------------------------------------
donePhase' :: String -> SolveM ()
---------------------------------------------------------------------------
donePhase' msg = lift $ do
  threadDelay 25000
  putBlankLn
  donePhase Loud msg
-}
