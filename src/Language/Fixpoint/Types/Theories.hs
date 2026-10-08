{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE DeriveDataTypeable         #-}

{-# OPTIONS_GHC -Wno-orphans            #-}
{-# OPTIONS_GHC -Wno-name-shadowing     #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Types.Theories (

    -- * Serialized Representation
      Raw

    -- * Theory Symbol
    , TheorySymbol (..)
    , Sem (..)

    -- * Theory Sorts
    , SmtSort (..)
    , FuncSort
    , DeclarationKey (..)
    , valueDeclarations
    , lookupDeclarations
    , sortSmtSort
    , sortSmtSortWithVars
    , resolveNumericKind
    , resolveNumericSort
    , isIntSmtSort

    , commitDeclarations

    -- * Symbol Environments
    , SymEnv (..)
    , emptySymEnv
    , SymM
    , freshSmtIndex
    , symEnv
    , symEnvSort
    , symEnvTheory
    , polyValueSort
    , isPolyValueSort
    , normalizeValueInstance
    , insertSymEnv
    , deleteSymEnv
    , insertsSymEnv
    , deletesSymEnv
    , symbolAtName
    , symbolAtSortIndex

    , TheorySymbols(..)
    ) where


import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           Data.Hashable
import           GHC.Generics              (Generic)
import           Control.Applicative
import           Control.Monad              (guard)
import           Control.Monad.State
import           Control.DeepSeq
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Names
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types.Environments

import           Text.PrettyPrint.HughesPJ.Compat
import qualified Data.List                as L
import           Data.Text (Text)
import qualified Data.Text                as Text
import qualified Data.Store              as S
import qualified Data.HashMap.Strict      as M
import qualified Language.Fixpoint.Misc   as Misc

--------------------------------------------------------------------------------
-- | 'Raw' is the low-level representation for SMT values
--------------------------------------------------------------------------------
type Raw = Text

--------------------------------------------------------------------------------
-- | 'SymEnv' is used to resolve the 'Sort' and 'Sem' of each 'Symbol'
--------------------------------------------------------------------------------

{- | Apply-carrier and nominal-value tags already declared in one SMT context.

The tags are organized in a stack because every time we pop the SMT solver
state, it forgets the tags declared since the last push.

Each entry maps declaration keys to fresh name indices. Every time we issue a `push` a new level
is added to the stack, and correspondingly, a `pop` removes a level.

See 'seDeclarationsCur' in 'SymEnv' for details about actually declaring the
tags to the SMT solver.
-}
type Declarations = [M.HashMap DeclarationKey Int]

lookupDeclarations :: DeclarationKey -> Declarations -> Maybe Int
lookupDeclarations fs = foldr (\hm acc -> acc <|> M.lookup fs hm) Nothing

commitDeclarations :: M.HashMap DeclarationKey Int -> Declarations -> Declarations
commitDeclarations m (top : rest) = (top <> m) : rest
commitDeclarations m [] = [m]

data SymEnv = SymEnv
    { seSort :: !(SEnv Sort)
    -- ^ Sorts of *all* defined symbols
    , seTheory :: !(SEnv TheorySymbol)
    -- ^ Information about theory-specific Symbols
    , seData :: !(SEnv DataDecl)
    -- ^ User-defined data-declarations
    , seLits :: !(SEnv Sort)
    -- ^ Distinct Constant symbols
    , seDeclarations :: !Declarations
    {- ^ Tags already declared in the SMT solver. Keys preserve either the
    apply carrier or the selected nominal value instance.
    -}
    , seDeclarationsCur :: !(M.HashMap DeclarationKey Int)
    {- ^ Tags requested while serializing the current command. Both kinds
    are declared before their first use, committed together to the current
    scope, and forgotten together on Pop.
    -}
    , seIx :: !Int
    -- ^ Largest unused index for sorts
    , seString :: !Bool
    -- ^ Use string literals
    , seSetBag :: !Bool
    -- ^ Encode source sets and bags as arrays at the SMT boundary.
    }
    deriving (Eq, Show, Data, Typeable, Generic)

{- type FuncSort = {v:Sort | isFFunc v} @-}
type FuncSort = (SmtSort, SmtSort)

-- Apply carriers erase source types; value families retain nominal instance identity.
data DeclarationKey = ApplyCarrier FuncSort | ValueInstance Symbol Sort
    deriving (Eq, Show, Data, Typeable, Generic)

instance Hashable DeclarationKey
instance NFData DeclarationKey
instance S.Store DeclarationKey

-- Project values using their nominal-key hashing rather than mixed-key iteration.
valueDeclarations :: M.HashMap DeclarationKey Int -> M.HashMap (Symbol, Sort) Symbol
valueDeclarations tags = M.fromList [((name, sort), intSymbol (symbol "lq_instantiated_value") index) | (ValueInstance name sort, index) <- M.toList tags]

{- | Generating SMT expressions is a stateful process because new symbols ('apply', 'coerce',
  'smt_lambda' and 'lam_arg') need to be emitted with unique ids for each newly encountered
  function sort. The 'SymM' monad carries the 'SymEnv' state required to track the ids.
  The state updates are performed in `L.F.Smt.Serialize` (functions `smt2App`, `smt2Coerc`,
  `smt2Lam` and `smtLamArg`, correspondingly).
-}
type SymM a = State SymEnv a

-- All allocators share this checked frontier; maxBound denotes exhaustion.
-- Pop restores an earlier frontier only after discarding its declaration frame.
freshSmtIndex :: (Int -> Bool) -> SymM Int
freshSmtIndex available = do
    env <- get
    case if seIx env < 0 then Nothing else L.find available [seIx env .. maxBound - 1] of
        Nothing -> Misc.errorstar "SMT symbol namespace exhausted"
        Just index -> put env{seIx = index + 1} >> pure index

instance NFData SymEnv
instance S.Store SymEnv

-- Declaration maps combine separately; emitted names belong to one solver context.
emptySymEnv :: SymEnv
emptySymEnv = SymEnv emptySEnv emptySEnv emptySEnv emptySEnv [] mempty 0 True False

symEnv :: Config -> SEnv Sort -> SEnv TheorySymbol -> [DataDecl] -> SEnv Sort -> SymEnv
symEnv cfg xEnv fEnv ds ls = SymEnv xEnv' fEnv dEnv ls [] mempty 0 seStr (elabSetBag (solverFlags cfg))
  where
    xEnv' = unionSEnv xEnv wiredInEnv
    dEnv = fromListSEnv [(symbol d, d) | d <- ds]
    seStr = not (noStringTheory cfg)

-- | These are "BUILT-in" polymorphic functions which are
--   UNINTERPRETED but POLYMORPHIC, hence need to go through
--   the apply-defunc stuff.
wiredInEnv :: M.HashMap Symbol Sort
wiredInEnv = M.fromList
  [ (toIntName, mkFFunc 1 [FVar 0, FInt])
  , (tyCastName, FAbs 0 $ FAbs 1 $ FFunc (FVar 0) (FVar 1))
  ]

symEnvTheory :: Symbol -> SymEnv -> Maybe TheorySymbol
symEnvTheory x env = lookupSEnv x (seTheory env)

symEnvSort :: Symbol -> SymEnv -> Maybe Sort
symEnvSort   x env = lookupSEnv x (seSort env)

-- A free nullary polymorphic value has one value per selected logical sort.
-- Callable schemes and interpreted theory constructors have other encodings.
polyValueSort :: SymEnv -> Symbol -> Maybe Sort
polyValueSort env x = do
  scheme <- symEnvSort x env
  guard (isPolyValueSort scheme)
  guard $ case symEnvTheory x env of
    Nothing -> True
    Just theory -> tsInterp theory == Uninterp
  pure scheme

isPolyValueSort :: Sort -> Bool
isPolyValueSort scheme = not (null variables) && case body of
  FFunc {} -> False
  FApp (FApp constructor _) _ | constructor == funcSort -> False
  _ -> True
  where
    (variables, body) = bkAbs scheme

-- This key preserves logical function structure even where SMT represents
-- both functions and ordinary objects as Int. Floating variables follow the
-- existing Int-erasure convention; tycons retain their native carrier metadata
-- while their existing nominal equality ignores source locations.
normalizeValueInstance :: Sort -> Maybe Sort
normalizeValueInstance = go
  where
    go FAbs{} = Nothing
    go FVar{} = Just FInt
    go FObj{} = Just FInt
    go (FFunc argument result) = go (FApp (FApp funcSort argument) result)
    go (FApp constructor argument) = FApp <$> go constructor <*> go argument
    go sort = Just sort

insertSymEnv :: Symbol -> Sort -> SymEnv -> SymEnv
insertSymEnv x t env = env { seSort = insertSEnv x t (seSort env) }

deleteSymEnv :: Symbol -> SymEnv -> SymEnv
deleteSymEnv x env = env { seSort = deleteSEnv x (seSort env) }

insertsSymEnv :: SymEnv -> [(Symbol, Sort)] -> SymEnv
insertsSymEnv = L.foldl' (\env (x, s) -> insertSymEnv x s env)

deletesSymEnv :: SymEnv -> [Symbol] -> SymEnv
deletesSymEnv = L.foldl' (\env x -> deleteSymEnv x env)

symbolAtSortIndex :: Symbol -> Int -> Text
symbolAtSortIndex mkSym si = appendSymbolText mkSym . Text.pack . show $ si

symbolAtName :: Symbol -> Sort -> SymM Text
symbolAtName mkSym s =
  do env <- get
     fsi <- funcSortIndex (ffuncSort env s)
     pure $ symbolAtSortIndex mkSym fsi
{-# SCC symbolAtName #-}

-- See 'seDeclarations' and 'seDeclarationsCur' in 'SymEnv' for explanation.
funcSortIndex :: FuncSort -> SymM Int
funcSortIndex fs =
  do
    env <- get
    case lookupDeclarations (ApplyCarrier fs) (seDeclarationsCur env : seDeclarations env) of
      Just i -> pure i
      Nothing ->
        do
          i <- freshSmtIndex (const True)
          modify (\current -> current{seDeclarationsCur = M.insert (ApplyCarrier fs) i (seDeclarationsCur current)})
          pure i

ffuncSort :: SymEnv -> Sort -> FuncSort
ffuncSort env t = {- tracepp ("ffuncSort " ++ showpp (t1,t2)) -} (tx t1, tx t2)
  where
    tx = applySmtSort env
    (t1, t2) = args t
    args (FFunc a b) = (a, b)
    args _ = (FInt, FInt)

applySmtSort :: SymEnv -> Sort -> SmtSort
applySmtSort = sortSmtSort False

isIntSmtSort :: SymEnv -> Sort -> Bool
isIntSmtSort env s = SInt == applySmtSort env s

--------------------------------------------------------------------------------

-- | 'TheorySymbol' represents the information about each interpreted 'Symbol'

--------------------------------------------------------------------------------
data TheorySymbol  = Thy
  { tsSym    :: !Symbol          -- ^ name
  , tsRaw    :: !Raw             -- ^ serialized SMTLIB2 name
  , tsSort   :: !Sort            -- ^ sort
  , tsInterp :: !Sem             -- ^ TRUE = defined (interpreted), FALSE = declared (uninterpreted)
  }
  deriving (Eq, Ord, Show, Data, Typeable, Generic)


class TheorySymbols a where
  theorySymbols :: a ->  SEnv TheorySymbol

instance NFData Sem
instance NFData TheorySymbol
instance S.Store TheorySymbol

instance PPrint Sem where
  pprintTidy _ = text . show

instance Fixpoint TheorySymbol where
  toFix (Thy x _ t d) = text "TheorySymbol" <+> pprint (x, t) <+> parens (pprint d)

instance PPrint TheorySymbol where
  pprintTidy k (Thy x _ t d) = text "TheorySymbol" <+> pprintTidy k (x, t) <+> parens (pprint d)

--------------------------------------------------------------------------------
-- | 'Sem' describes the SMT semantics for a given symbol
--------------------------------------------------------------------------------

data Sem
  = Uninterp      -- ^ for UDF: `len`, `height`, `append`
  | Ctor          -- ^ for ADT constructor and tests: `cons`, `nil`
  | Test          -- ^ for ADT tests : `is$cons`
  | Field         -- ^ for ADT field: `hd`, `tl`
  | Theory        -- ^ for theory ops: mem, cup, select
  | Defined       -- ^ for user-defined `define-fun`
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance S.Store Sem


--------------------------------------------------------------------------------
-- | A Refinement of 'Sort' that describes SMTLIB Sorts
--------------------------------------------------------------------------------
data SmtSort
  = SInt
  | SBool
  | SReal
  | SString
  --- CVC(5) only
  | SSet !SmtSort
  | SBag !SmtSort
  | SFFld !Integer
  ---
  | SArray !SmtSort !SmtSort
  | SBitVec !Int
  | SVar    !Int
  | SData   !FTycon ![SmtSort]
  -- HKT | SApp            ![SmtSort]           -- ^ Representing HKT
  deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance Hashable SmtSort
instance NFData   SmtSort
instance S.Store SmtSort

-- | The 'poly' parameter is True when we are *declaring* sorts,
--   and so we need to leave the top type variables be; it is False when
--   we are declaring variables etc., and there, we serialize them
--   using `Int` (though really, there SHOULD BE NO floating tyVars...
--   'smtSort True  msg t' serializes a sort 't' using type variables,
--   'smtSort False msg t' serializes a sort 't' using 'Int' instead of tyvars.
sortSmtSort :: Bool -> SymEnv -> Sort -> SmtSort
sortSmtSort poly env t = sortSmtSortUsing variable poly env t
  where
    m = sortAbs t
    variable i
        | poly, i < m = SVar i
        | otherwise = SInt

-- Preserve selected variable origins while using the same native value
-- translation, including erased arguments and datatype parameter padding.
sortSmtSortWithVars :: (Int -> SmtSort) -> SymEnv -> Sort -> SmtSort
sortSmtSortWithVars variable = sortSmtSortUsing variable False

sortSmtSortUsing :: (Int -> SmtSort) -> Bool -> SymEnv -> Sort -> SmtSort
sortSmtSortUsing variable poly env t = go . resolveNumericKind (`lookupSEnv` seSort env) . unAbs $ t
  where
    go (FFunc _ _) = SInt
    go FInt = SInt
    go FReal = SReal
    go t
        | t == boolSort = SBool
        | isString t = SString
    go (FVar i) = variable i
    go t
        | (ct : ts) <- unFApp t = fappSmtSort variable poly env ct ts
        | otherwise = error "Unexpected empty 'unFApp t'"

-- Explicit numeric-kind declarations fix an abstract scalar's representation.
-- This is not inferred from a nominal constructor's Num/Fractional metadata.
resolveNumericKind :: (Symbol -> Maybe Sort) -> Sort -> Sort
resolveNumericKind lookupKind sort@(FObj name) = case lookupKind name of
    Just FFrac -> FReal
    Just FReal -> FReal
    Just FNum -> FInt
    Just FInt -> FInt
    _ -> sort
resolveNumericKind _ sort = sort

-- Capture aliases while their declaration scope is still available. The
-- resulting sort keeps its meaning when carried beneath a shadowing binder
-- or out to a deferred declaration.
resolveNumericSort :: (Symbol -> Maybe Sort) -> Sort -> Sort
resolveNumericSort lookupKind = substSort (resolveNumericKind lookupKind . FObj)

fappSmtSort :: (Int -> SmtSort) -> Bool -> SymEnv -> Sort -> [Sort] -> SmtSort
fappSmtSort variable poly env = go
  where
    -- Argument translation retains the enclosing variable interpretation.
    go (FTC c) [a]
        | setConName == symbol c =
            if seSetBag env then SArray (sortSmtSortUsing variable poly env a) SBool else SSet (sortSmtSortUsing variable poly env a)
    go (FTC c) [a]
        | bagConName == symbol c =
            if seSetBag env then SArray (sortSmtSortUsing variable poly env a) SInt else SBag (sortSmtSortUsing variable poly env a)
    go (FTC c) [FNatNum n]
        | ffldConName == symbol c = SFFld n
    go (FTC c) [a, b]
        | arrayConName == symbol c || mapConName == symbol c = SArray (sortSmtSortUsing variable poly env a) (sortSmtSortUsing variable poly env b)
    go (FTC bv) [FTC s]
        | bitVecName == symbol bv
        , Just n <- sizeBv s =
            SBitVec n
    go s []
        | isString s = SString
    go (FTC c) ts
        | Just n <- tyArgs c (seData env)
        , let i = n - length ts =
            SData c ((sortSmtSortUsing variable poly env <$> ts) ++ pad i)
    go _ _ = SInt

    pad i
        | poly = []
        | otherwise = replicate i SInt

tyArgs :: (Symbolic x) => x -> SEnv DataDecl -> Maybe Int
tyArgs x env = ddVars <$> lookupSEnv (symbol x) env

instance PPrint SmtSort where
  pprintTidy _ SInt         = text "Int"
  pprintTidy _ SBool        = text "Bool"
  pprintTidy _ SReal        = text "Real"
  pprintTidy _ SString      = text "Str"
  pprintTidy k (SSet a)     = ppParens k (text "Set") [a]
  pprintTidy k (SBag a)     = ppParens k (text "Bag") [a]
  pprintTidy _ (SFFld n)    = text "FiniteField" <+> integer n
  pprintTidy k (SArray a b) = ppParens k (text "Array") [a, b]
  pprintTidy _ (SBitVec n)  = text "BitVec" <+> int n
  pprintTidy _ (SVar i)     = text "@" <-> int i
--  HKT pprintTidy k (SApp ts)    = ppParens k (pprintTidy k tyAppName) ts
  pprintTidy k (SData c ts) = ppParens k (pprintTidy k c)         ts

ppParens :: (PPrint d) => Tidy -> Doc -> [d] -> Doc
ppParens k d ds = parens $ Misc.intersperse (text "") (d : (pprintTidy k <$> ds))
