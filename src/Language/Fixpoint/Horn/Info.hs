{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}

module Language.Fixpoint.Horn.Info (
    hornFInfo
  , scrapeFInfo
  ) where

import           Data.Ord (Down(..), comparing)
import qualified Data.HashMap.Strict            as M
import qualified Data.HashSet                   as S
import qualified Data.List                      as L
import qualified Data.Tuple                     as Tuple
import           GHC.Generics                   (Generic)
import qualified Language.Fixpoint.SortCheck    as SortCheck
import qualified Language.Fixpoint.Misc         as Misc
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Types.Config as F
import qualified Language.Fixpoint.Horn.Types   as H
import qualified Language.Fixpoint.Types.Visitor as V
import qualified Data.Maybe                     as Mb

hornFInfo :: (F.Fixpoint a, F.PPrint a) => F.Config -> H.Query a -> F.FInfo a
hornFInfo cfg q = mempty
  { F.cm        = cs
  , F.bs        = be2
  , F.ws        = kvEnvWfCs kve
  , F.quals     = H.qQuals q ++ scrapeCstr (F.scrape cfg) hCst
  , F.gLits     = F.fromMapSEnv $ H.qCon q
  , F.dLits     = F.fromMapSEnv $ H.qDis q
  , F.ae        = axEnv cfg q cs
  , F.ddecls    = H.qData q
  , F.hoInfo    = F.cfgHoInfo cfg
  , F.defns     = F.MkDefinedFuns (H.qDefs q)
  , F.kuts      = F.KS (S.fromList (H.qKuts q))
  , F.asserts   = H.qAxioms q
  }
  where
    be0         = F.emptyBindEnv
    (be1, kve)  = hornWfs   be0     (H.qVars q)
    (be2, cs) = hornSubCs be1 kve hCst
    hCst           = H.qCstr q


axEnv :: F.Config -> H.Query a -> M.HashMap F.SubcId b -> F.AxiomEnv
axEnv cfg q cs = mempty
  { F.aenvEqs    = H.qEqns q
  , F.aenvSimpl  = H.qMats q
  , F.aenvExpand = if F.rewriteAxioms cfg then True <$ cs else mempty
  }

----------------------------------------------------------------------------------
hornSubCs :: F.BindEnv a -> KVEnv a -> H.Cstr a
          -> (F.BindEnv a, M.HashMap F.SubcId (F.SubC a))
----------------------------------------------------------------------------------
hornSubCs be kve c = (be', M.fromList (F.addIds cs))
  where
    (be', cs) = goS kve F.emptyIBindEnv be c
    -- lhs0           = bindSortedReft kve H.dummyBind

-- | @goS@ recursively traverses the NNF constraint to build up a list
--   of the vanilla @SubC@ constraints.

goS :: KVEnv a -> F.IBindEnv ->  F.BindEnv a -> H.Cstr a
    -> (F.BindEnv a, [F.SubC a])

goS kve env be c = (be', subcs)
  where
    (be', subcs) = goS' kve env Nothing be c

goS' :: KVEnv a -> F.IBindEnv -> Maybe F.SortedReft -> F.BindEnv a -> H.Cstr a
    -> (F.BindEnv a, [F.SubC a])
goS' kve env lhs be (H.Head p l) = (be, [subc])
  where
    subc                        = myMkSubC env lhs rhs Nothing [] l
    rhs                         = updSortedReft kve lhs p

goS' kve env lhs be (H.CAnd cs)  = (be', concat subcss)
  where
    (be', subcss)               = L.mapAccumL (goS' kve env lhs) be cs

goS' kve env _   be (H.All b c)  = (be'', subcs)
  where
    (be'', subcs)               = goS' kve env' (Just bSR) be' c
    (bId, be')                  = F.insertBindEnv (H.bSym b) bSR (H.bMeta b) be
    bSR                         = bindSortedReft kve b
    env'                        = F.insertsIBindEnv [bId] env

myMkSubC :: F.IBindEnv -> Maybe F.SortedReft -> F.SortedReft -> Maybe Integer -> F.Tag -> a -> F.SubC a
myMkSubC be lhsMb rhs x y z = F.mkSubC be lhs rhs x y z
  where
    lhs = Mb.fromMaybe def lhsMb
    def = F.trueSortedReft (F.sr_sort rhs)

bindSortedReft :: KVEnv a -> H.Bind a -> F.SortedReft
bindSortedReft kve (H.Bind x t p _) = F.RR t (F.Reft (x, predExpr kve p))

updSortedReft :: KVEnv a -> Maybe F.SortedReft -> H.Pred -> F.SortedReft
updSortedReft kve lhs p = F.RR s (F.Reft (v, predExpr kve p))
   where
      (s, v) = case lhs of
                 Just (F.RR ss (F.Reft (vv, _))) -> (ss, vv)
                 Nothing                       -> (F.intSort, F.dummySymbol)

predExpr :: KVEnv a -> H.Pred -> F.Expr
predExpr kve        = go
  where
    go (H.Reft  e ) = e
    go (H.Var k ys) = kvApp kve k ys
    go (H.PAnd  ps) = F.PAnd (go <$> ps)

kvApp :: KVEnv a -> F.Symbol -> [F.Expr] -> F.Expr
kvApp kve k ys = F.PKVar (F.KV k) M.empty su
  where
    su         = F.mkKVarSubst (zip params ys)
    params     = maybe err1 kvParams (M.lookup k kve)
    err1       = F.panic ("Unknown Horn variable: " ++ F.showpp k)

----------------------------------------------------------------------------------
hornWfs :: (F.PPrint a) => F.BindEnv a -> [H.Var a] -> (F.BindEnv a, KVEnv a)
----------------------------------------------------------------------------------
hornWfs be vars = (be', kve)
  where
    kve         = M.fromList [ (kname i, i) | i <- is ]
    (be', is)   = L.mapAccumL kvInfo be vars
    kname       = H.hvName . kvVar

kvInfo :: (F.PPrint a) => F.BindEnv a -> H.Var a -> (F.BindEnv a, KVInfo a)
kvInfo be k       = (be', KVInfo k (Misc.fst3 <$> xts) wfc)
  where
    -- make the WfC
    wfc           = F.WfC wenv vvs (F.KV (H.hvName k)) (H.hvMeta k)
    wenv          = F.fromListIBindEnv ids
    -- the self parameters are the value variables, and the rest are binders
    vvs           = [ (x, t) | (x, t, _) <- selfs ]
    (selfs, xts') = splitAt (H.hvSelf k) xts
    -- add the binders
    (be', ids)    = L.mapAccumL insertBE be xts'
    -- make the parameters
    xts           = [ (hvarArg k i, t', a) | (t', i) <- zip (H.hvArgs k) [0..] ]
    a             = H.hvMeta k

insertBE :: F.BindEnv a -> (F.Symbol, F.Sort, a) -> (F.BindEnv a, F.BindId)
insertBE be (x, t, a) = Tuple.swap $ F.insertBindEnv x (F.trueSortedReft t) a be

----------------------------------------------------------------------------------
-- | Data types and helpers for manipulating information about KVars
----------------------------------------------------------------------------------
type KVEnv a  = M.HashMap F.Symbol (KVInfo a)

data KVInfo a = KVInfo
  { kvVar    :: !(H.Var a)
  , kvParams :: ![F.Symbol]
  , kvWfC    :: !(F.WfC a)
  }
  deriving (Generic, Functor)

kvEnvWfCs :: KVEnv a -> M.HashMap F.KVar (F.WfC a)
kvEnvWfCs kve = M.fromList [ (F.KV k, kvWfC info) | (k, info) <- M.toList kve ]

hvarArg :: H.Var a -> Int -> F.Symbol
hvarArg k i = F.hvarArgSymbol (H.hvName k) i

-------------------------------------------------------------------------------
-- | Automatically scrape qualifiers from all predicates in a constraint

-------------------------------------------------------------------------------

-- Reuse the Horn qualifier language for ordinary subtyping constraints.
-- These expressions supply candidates only; their original polarity and
-- proof obligations remain unchanged in the FInfo passed to the solver.
-- A candidate depends only on its predicate's free declarations. Project each
-- constraint's scope onto that support, preserving lhs shadowing and the Horn
-- scraper's cyclic parameter order without rebuilding the complete scope.
scrapeFInfo :: F.Config -> F.Scrape -> F.FInfo a -> [F.Qualifier]
scrapeFInfo _ F.No _ = []
scrapeFInfo cfg mode info = Misc.sortNub $ filter closed $ concatMap (uncurry mkQualParams) inputs
  where
    inputs = S.toList $ S.fromList $ concatMap scrapeSub constraints ++ environmentInputs
    constraints = M.elems (F.cm info)
    -- Environment facts depend on their scope and the lhs declaration, not
    -- the constraint's own predicates. Share only that exact judgment.
    contexts = S.toList $ S.fromList $ map context constraints
    environmentInputs = case mode of
        F.Both -> concatMap scrapeScope contexts
        _ -> []
    bindings = F.beBinds (F.bs info)
    -- envCs restricts this enumeration without reordering it. Reversing each
    -- name's declarations retains its last in-scope binding, including duplicates.
    declarations = M.fromListWith (++) [(name, [(i, sort)]) | (i, (name, F.RR sort _, _)) <- M.toList bindings]
    facts = fmap (\(name, reft, _) -> candidates (predicateAt name reft)) bindings
    candidates e = [(p, S.toList (F.syms p)) | p <- scrapeConjuncts e, V.isConc p]
    -- Inference candidates may mention only their parameters and this query's
    -- globals. Predicates from a local environment can outlive a local symbol
    -- in the raw BindEnv; they are not new globally scoped declarations.
    closed = all (`F.memberSEnv` globals) . F.syms
    globals = SortCheck.globalEnv cfg info
    context sub = (F.senv sub, value, sort)
      where
        F.RR sort (F.Reft (value, _)) = F.slhs sub
    scrapeSub sub = project (context sub) predicates
      where
        lhs@(F.RR _ (F.Reft (value, _))) = F.slhs sub
        predicates =
            candidates (predicateAt value (F.srhs sub)) ++ case mode of
                F.Both -> candidates (predicateAt value lhs)
                _ -> []
    scrapeScope scope@(bindingsInScope, _, _) =
        project
            scope
            (concat [ps | i <- F.elemsIBindEnv bindingsInScope, Just ps <- [M.lookup i facts]])
    project (scope, value, sort) predicates =
        [ (L.sortOn (\(x, _) -> Down (x == value, x)) xts, p)
        | (p, names) <- predicates
        , let xts = parameters names
        , not (null xts)
        , length xts <= maxQualifierParams
        ]
      where
        -- shiftCycle emits nothing at these rejected arities. Admit only its
        -- productive inputs before sorting parameters or hashing predicates.
        parameters names = take (maxQualifierParams + 1) [(x, t) | x <- names, Just t <- [lookupSort x]]
        lookupSort x
            | x == value = Just sort
            | otherwise = Mb.listToMaybe [t | (i, t) <- M.lookupDefault [] x declarations, F.memberIBindEnv i scope]
    predicateAt name (F.RR _ (F.Reft (value, predicate))) = F.subst1 predicate (value, F.EVar name)

scrapeCstr :: F.Scrape -> H.Cstr a -> [F.Qualifier]
scrapeCstr F.No _    = []
scrapeCstr m    cstr = Misc.sortNub $ go emptyBindEnv cstr
  where
    go senv (H.Head p _) = scrapePred senv p
    go senv (H.CAnd cs)  = concatMap (go senv) cs
    go senv (H.All b c)  = scrapeBind m senv' b <> go senv' c where senv' = insertBindEnv b senv

scrapeBind :: F.Scrape -> BindEnv -> H.Bind a -> [F.Qualifier]
scrapeBind F.Both senv b = scrapePred senv (H.bPred b)
scrapeBind _      _    _ = []

scrapePred :: BindEnv -> H.Pred -> [F.Qualifier]
scrapePred _    (H.Var _ _) = []
scrapePred senv (H.PAnd ps) = concatMap (scrapePred senv) ps
scrapePred senv (H.Reft e)  = concatMap (mkQual senv) (scrapeConjuncts e)

-- Retain original templates: their first parameter anchors instantiation.
-- In total Boolean logic, ite p q false also supplies the conjuncts of p and q.
scrapeConjuncts :: F.Expr -> [F.Expr]
scrapeConjuncts = concatMap candidates . F.concConjuncts
  where
    candidates e@(F.EIte p q F.PFalse) = e : conjuncts p ++ conjuncts q
    candidates e = [e]
    conjuncts (F.PAnd ps) = concatMap conjuncts ps
    conjuncts (F.EIte p q F.PFalse) = conjuncts p ++ conjuncts q
    conjuncts e = F.concConjuncts e

-- NOTE: Constraints.mkQual will do extra stuff like generalizing the sorts...
mkQual :: BindEnv -> F.Expr -> [F.Qualifier]
mkQual env e = mkQualParams (qualParams env e) e

mkQualParams :: [(F.Symbol, F.Sort)] -> F.Expr -> [F.Qualifier]
mkQualParams xts e
  -- Qualifiers are fixed predicates, not definitions of the unknowns whose
  -- source constraints we are mining. Leave those constraints untouched.
  | V.isConc e = [mkScrapeQual xts' e | xts' <- shiftCycle xts]
  | otherwise = []

mkScrapeQual :: [(F.Symbol, F.Sort)] -> F.Expr -> F.Qualifier
mkScrapeQual xts e = F.mkQual (F.symbol "AUTO") qParams body (F.dummyPos "")
  where
    qParams = [ F.QP {F.qpSym = y, F.qpPat = F.PatNone, F.qpSort = t} | (_, y, t) <- xyts ]
    xyts    = zipWith (\i (x, t) -> (x, F.bindSymbol i, t)) [0..] xts
    su      = F.mkSubst [ (x, F.expr y) | (x, y, _) <- xyts ]
    body    = F.subst su e


shiftCycle :: [(F.Symbol, F.Sort)] -> [[(F.Symbol, F.Sort)]]
shiftCycle xts
  | n <= maxQualifierParams = recycle n xts
  | otherwise              = []
  where
    n                      = length xts

recycle :: Int -> [a] -> [[a]]
recycle 0 _      = []
recycle _ []     = []
recycle k (x:xs) = (x:xs) : recycle (k-1) (xs ++ [x])

maxQualifierParams :: Int
maxQualifierParams = 3

{-
  1. Normalize the names
  2. Permute the args?
 -}

qualParams :: BindEnv -> F.Expr -> [(F.Symbol, F.Sort)]
qualParams env e = [ (x, t) | (_, x, t) <- L.sortBy (comparing Down) ixts ]
  where
    xs = S.toList (F.syms e)
    ixts = [ (i, x, t) | x <- xs, (t, i) <- Mb.maybeToList (lookupBindEnv x env) ]

-------------------------------------------------------------------------------

-- | `BindEnv` maps each symbol to (sort, depth) pair, where shorter depths
--    means bound "earlier" i.e. in (forall (x1:...) (forall (x2:...) ...)
--    the depth of x1 is less than the depth of x2.
--    We use the heuristic that the symbol with the "largest" depth is the
--    "value-variable" in the qualifier.

data BindEnv = BindEnv
  { bSize  :: !Int
  , bBinds :: M.HashMap F.Symbol (F.Sort, Int)
  }

emptyBindEnv :: BindEnv
emptyBindEnv = BindEnv { bSize = 0, bBinds = mempty }

insertBindEnv :: H.Bind a -> BindEnv -> BindEnv
insertBindEnv b senv = BindEnv { bSize = n + 1, bBinds = M.insert x (t, n) (bBinds senv) }
  where
    n = bSize senv
    x = H.bSym b
    t = H.bSort b

lookupBindEnv :: F.Symbol -> BindEnv -> Maybe (F.Sort, Int)
lookupBindEnv x env = M.lookup x (bBinds env)
