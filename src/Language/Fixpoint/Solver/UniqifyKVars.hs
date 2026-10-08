{-# LANGUAGE CPP                    #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{- | This module creates new bindings for each argument of each kvar.
     It also makes sure that all arguments to each kvar are explicit.

     For example,

```
bind 0 x
bind 1 v
constraint:
  env [0; 1]
  rhs $k_42 // implicit substitutions [x:=x], [v:=v]
wf:
  env [0]
  reft {v : int | [$k_42]}
```

becomes

```
bind 0 x
bind 1 v
bind 2 lq_karg$x$k_42
constraint:
  env [0; 1]
  rhs $k_42[lq_karg$x$k_42:=x][lq_karg$v$k_42:=v]

wf:
  env [2]
  reft {lq_karg$v$k_42 : int | [$k_42]}
```

-}

module Language.Fixpoint.Solver.UniqifyKVars (wfcUniqify, FormalOrigin (..), WfOrigins, occupiedSymbols) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor (mapKVarSubsts)
import qualified Language.Fixpoint.Smt.Theories as Thy
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.List as L
#if !MIN_VERSION_base(4,20,0)
import           Data.Foldable       (foldl')
#endif

--------------------------------------------------------------------------------
wfcUniqify :: SInfo a -> (WfOrigins, SInfo a)
wfcUniqify fi = updateWfcs names $ remakeSubsts names fi
  where
    names = formalNames fi

-- Every generated formal must be outside the source declaration namespace,
-- including the names of other KVar formals already allocated in this query.
occupiedSymbols :: SInfo a -> S.HashSet Symbol
occupiedSymbols fi = S.fromList $ binders ++ values ++ globals ++ map fst (toListSEnv declared)
  where
    binders = [sym | (_, (sym, _, _)) <- bindEnvToList (bs fi)]
    values = [v | w <- M.elems (ws fi), let (v, _, _) = wrft w]
    globals = map fst (toListSEnv (gLits fi) ++ toListSEnv (dLits fi))
    declared = Thy.theorySymbols (ddecls fi) <> Thy.theorySymbols (defns fi) <> Thy.theorySymbols (aenvEqs (ae fi))

type FormalNames = M.HashMap KVar (M.HashMap Symbol Symbol)

data FormalOrigin = ValueOrigin !Symbol !BindId | BindOrigin !Symbol !BindId
  deriving (Eq, Show)

type WfOrigins = M.HashMap KVar [FormalOrigin]

formalNames :: SInfo a -> FormalNames
formalNames fi = snd $ L.foldl' allocateKVar (occupiedSymbols fi, M.empty) (L.sort $ M.keys $ ws fi)
  where
    allocateKVar (used, allNames) k = (used', M.insert k names allNames)
      where
        (used', names) = L.foldl' (allocate k) (used, M.empty) (L.sort $ kvarDomain fi k)
    allocate k (used, names) source
        | M.member source names = (used, names)
        | otherwise =
            let (used', target) = freshInNS (kArgSymbol source (kv k)) used
             in (used', M.insert source target names)

formalName :: FormalNames -> KVar -> Symbol -> Symbol
formalName names k source = M.lookupDefault (kArgSymbol source (kv k)) source (M.lookupDefault M.empty k names)

-- mapKVarSubsts (\k su -> restrict table k su xs)
--------------------------------------------------------------------------------
remakeSubsts :: FormalNames -> SInfo a -> SInfo a
--------------------------------------------------------------------------------
remakeSubsts names fi = mapKVarSubsts (remakeSubst names fi) fi

remakeSubst :: FormalNames -> SInfo a -> KVar -> KVarSubst Symbol Symbol -> KVarSubst Symbol Symbol
remakeSubst names fi k su = toKVarSubst $ M.union translated untouched
  where
    actuals = fromKVarSubst su
    domain = kvarDomain fi k
    oldNames = S.fromList domain
    translated = M.fromList [(formalName names k source, M.lookupDefault (eVar source) source actuals) | source <- domain]
    untouched = M.filterWithKey (\source _ -> not (S.member source oldNames)) actuals

--------------------------------------------------------------------------------
updateWfcs :: FormalNames -> SInfo a -> (WfOrigins, SInfo a)
--------------------------------------------------------------------------------
updateWfcs names fi = L.foldl' (\state (k, w) -> updateWfc names state k w) (M.empty, fi) (L.sortOn fst $ M.toList $ ws fi)

updateWfc :: FormalNames -> (WfOrigins, SInfo a) -> KVar -> WfC a -> (WfOrigins, SInfo a)
updateWfc names (origins, fi) k w = (M.insert k (ValueOrigin v valueId : reverse binderOrigins) origins, fi''{ws = M.insert k w' (ws fi)})
  where
    w' = w{wenv = insertsIBindEnv newIds mempty, wrft = (v', t, k)}
    (valueId, fi'') = newTopBind v' (trueSortedReft t) a fi'
    (fi', newIds, binderOrigins) = foldl' (accumBindsIfValid names k a) (fi, [], []) (L.sort $ elemsIBindEnv $ wenv w)
    (v, t, k) = wrft w
    v' = formalName names k v
    a = winfo w

accumBindsIfValid :: FormalNames -> KVar -> a -> (SInfo a, [BindId], [FormalOrigin]) -> BindId -> (SInfo a, [BindId], [FormalOrigin])
accumBindsIfValid names k a (fi, ids, origins) i =
    if renamable then accumBinds names k a (fi, ids, origins) i else (fi, i : ids, BindOrigin oldSym i : origins)
  where
    (oldSym, sr, _) = lookupBindEnv i (bs fi)
    renamable = isValidInRefinements (sr_sort sr)

accumBinds :: FormalNames -> KVar -> a -> (SInfo a, [BindId], [FormalOrigin]) -> BindId -> (SInfo a, [BindId], [FormalOrigin])
accumBinds names k a (fi, ids, origins) i = (fi', i' : ids, BindOrigin oldSym i' : origins)
  where
    (oldSym, sr, _) = lookupBindEnv i (bs fi)
    newSym = formalName names k oldSym
    (i', fi') = newTopBind newSym sr a fi

-- | `newTopBind` ignores the actual refinements as they are not relevant
--   in the kvar parameters (as suggested by BLC.)
newTopBind :: Symbol -> SortedReft -> a -> SInfo a -> (BindId, SInfo a)
newTopBind x sr a fi = (i', fi {bs = be'})
  where
    (i', be')        = insertBindEnv x (sr {sr_reft = trueReft}) a (bs fi)

--------------------------------------------------------------

isValidInRefinements :: Sort -> Bool
isValidInRefinements FInt        = True
isValidInRefinements FReal       = True
isValidInRefinements FNum        = False
isValidInRefinements FFrac       = False
isValidInRefinements (FObj _)    = True
isValidInRefinements (FVar _)    = True
isValidInRefinements (FFunc _ _) = True -- False
isValidInRefinements (FAbs  _ t) = isValidInRefinements t
isValidInRefinements (FTC _)     = True -- TODO is this true? seems to be required for e.g. ResolvePred.hs
isValidInRefinements (FApp _ _)  = True
isValidInRefinements (FNatNum _) = True -- TODO probably?
