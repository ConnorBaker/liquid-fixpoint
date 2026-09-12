{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DoAndIfThenElse      #-}

{-# OPTIONS_GHC -Wno-orphans        #-}

-- | This module contains the code for serializing Haskell values
--   into SMTLIB2 format, that is, the instances for the @SMTLIB2@
--   typeclass. We split it into a separate module as it depends on
--   Theories (see @smt2App@).

module Language.Fixpoint.Smt.Serialize (smt2SortMono) where

import           Control.Monad.State
import           Data.ByteString.Builder (Builder)
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Types.Visitor as Vis
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy

-- import           Data.Text.Format
import           Language.Fixpoint.Misc (sortNub, errorstar)
import           Language.Fixpoint.Utils.Builder as Builder
import qualified Data.Text as T
import qualified Data.HashSet as HS
import Data.Text (Text)
-- import Debug.Trace (trace)

instance SMTLIB2 (Symbol, Sort) where
  smt2 c@(sym, t) =
    -- build "({} {})" (smt2 env sym, smt2SortMono c env t)
    do s <- smt2 sym
       ss <- smt2SortMono c t
       pure $ parenSeqs [s , ss]

instance SMTLIB2 (Symbol, Expr) where
  smt2 (sym, e) =
    do s <- smt2 sym
       ss <- smt2 e
       pure $ parenSeqs [s, ss]

smt2SortMono, smt2SortPoly :: (PPrint a) => a -> Sort -> SymM Builder
smt2SortMono = smt2Sort False
smt2SortPoly = smt2Sort True

smt2Sort :: (PPrint a) => Bool -> a -> Sort -> SymM Builder
smt2Sort poly _ t =
  do env <- get
     smt2 (Thy.sortSmtSort poly (seData env) t)

smt2data :: [DataDecl] -> SymM Builder
smt2data = smt2data' . map padDataDecl

smt2data' :: [DataDecl] -> SymM Builder
smt2data' ds =
  do n <- traverse smt2dataname ds
     d <- traverse smt2datactors ds
     pure $ seqs [ parens $ smt2many n , parens $ smt2many d ]


smt2dataname :: DataDecl -> SymM Builder
smt2dataname (DDecl tc as _) =
  do name <- smt2 (symbol tc)
     n    <- smt2 as
     pure $ parenSeqs [name, n]


smt2datactors :: DataDecl -> SymM Builder
smt2datactors (DDecl _ as cs) =
  do ds <- traverse (smt2ctor as) cs
     if as > 0
      then do tvars <- traverse smt2TV [0..(as-1)]
              pure $ parenSeqs ["par", parens (smt2many tvars), parens (smt2many ds)]
      else pure $                                               parens (smt2many ds)
  where
    smt2TV = smt2 . SVar

smt2ctor :: Int -> DataCtor -> SymM Builder
smt2ctor as (DCtor c fs) =
  do h <- smt2 c
     t <- traverse (smt2field as) fs
     pure $ parenSeqs (h : t)

smt2field :: Int -> DataField -> SymM Builder
smt2field as d@(DField x t) =
  do s <- smt2 x
     ss <- smt2SortPoly d $ mkPoly as t
     pure $ parenSeqs [s , ss]

-- | SMTLIB/Z3 don't like "unused" type variables; they get pruned away and
--   cause wierd hassles. See tests/pos/adt_poly_dead.fq for an example.
--   'padDataDecl' adds a junk constructor that "uses" up all the tyvars just
--   to avoid this pruning problem.

padDataDecl :: DataDecl -> DataDecl
padDataDecl d@(DDecl tc n cs)
  | hasDead    = DDecl tc n (junkDataCtor tc n : cs)
  | otherwise  = d
  where
    hasDead    = length usedVars < n
    usedVars   = declUsedVars d

junkDataCtor :: FTycon -> Int -> DataCtor
junkDataCtor c n = DCtor (atLoc c junkc) [DField (junkFld i) (FVar i) | i <- [0..(n-1)]]
  where
    junkc        = suffixSymbol "junk" (symbol c)
    junkFld i    = atLoc c    (intSymbol junkc i)

declUsedVars :: DataDecl -> [Int]
declUsedVars = sortNub . Vis.foldDataDecl go []
  where
    go is (FVar i) = i : is
    go is _        = is

instance SMTLIB2 Symbol where
  smt2 s = do env <- get
              case Thy.smt2Symbol env s of
                Just t  -> pure t
                Nothing -> pure $ symbolBuilder s
instance SMTLIB2 Int where
  smt2 i = pure $ Builder.fromString $ show i

instance SMTLIB2 LocSymbol where
  smt2 = smt2 . val

instance SMTLIB2 SymConst where
  smt2 c@(SL t) = do
    seStr <- gets seString
    if seStr
      then pure $ quotes $ fromText $ smtEscape t  -- emit "hello" not lit$36$hello
      else smt2 (symbol c)

-- | Per https://smt-lib.org/theories-UnicodeStrings.shtml
-- "SMT-LIB 2.6 has one escape sequence of its own for string literals. Two
--  double quotes ("") are used to represent the double-quote character within
--  a string literal"

smtEscape :: Text -> Text
smtEscape = T.replace "\"" "\"\""

instance SMTLIB2 Constant where
  smt2 (I n)   = pure $ bShow n
  smt2 (R d)   = pure $ bFloat d
  smt2 (L t s)
    | isString s = pure $ quotes $ fromText t
    | otherwise  = pure $ fromText t

instance SMTLIB2 Bop where
  smt2 Plus   = pure "+"
  smt2 Minus  = pure "-"
  smt2 Times  = pure $ symbolBuilder mulFuncName
  smt2 Div    = pure $ symbolBuilder divFuncName
  smt2 RTimes = pure "*"
  smt2 RDiv   = pure "/"
  smt2 Mod    = pure "mod"

instance SMTLIB2 Brel where
  smt2 Eq  = pure "="
  smt2 Ueq = pure "="
  smt2 Gt  = pure ">"
  smt2 Ge  = pure ">="
  smt2 Lt  = pure "<"
  smt2 Le  = pure "<="
  smt2 _   = errorstar "SMTLIB2 Brel"

-- NV TODO: change the way EApp is printed
instance SMTLIB2 Expr where
  smt2 (ESym z) = smt2 z
  smt2 (ECon c) = smt2 c
  smt2 (EVar x) = do
    env <- get
    case polyValueSort env x of
      Just _ -> unresolvedPolyValue x
      Nothing -> smt2 x
  smt2 e@(EApp _ _) = smt2App e
  smt2 (ENeg e) = do
    s <- smt2 e
    pure $ parenSeqs ["-", s]
  smt2 (EBin o e1 e2) = do
    so <- smt2 o
    s1 <- smt2 e1
    s2 <- smt2 e2
    pure $ parenSeqs [so, s1, s2]
  smt2 (ELet x e1 e2) = do
    initializer <- smt2 e1
    withSmtShadowing [x] $ do
      name <- smt2 x
      body <- smt2 e2
      pure $ parenSeqs ["let", parens (parenSeqs [name, initializer]), body]
  smt2 (EIte e1 e2 e3) = do
    s1 <- smt2 e1
    s2 <- smt2 e2
    s3 <- smt2 e3
    pure $ parenSeqs ["ite", s1, s2, s3]
  smt2 (ECst e t) = smt2Cast e t
  smt2 PTrue = pure "true"
  smt2 PFalse = pure "false"
  smt2 (PAnd []) = pure "true"
  smt2 (PAnd ps) = do
    s <- smt2s ps
    pure $ parenSeqs ["and", s]
  smt2 (POr []) = pure "false"
  smt2 (POr ps) = do
    s <- smt2s ps
    pure $ parenSeqs ["or", s]
  smt2 (PNot p) = do
    s <- smt2 p
    pure $ parenSeqs ["not", s]
  smt2 (PImp p q) = do
    s1 <- smt2 p
    s2 <- smt2 q
    pure $ parenSeqs ["=>", s1, s2]
  smt2 (PIff p q) = do
    s1 <- smt2 p
    s2 <- smt2 q
    pure $ parenSeqs ["=", s1, s2]
  smt2 (PExist [] p) = smt2 p
  smt2 (PExist xs p) = smt2Quantifier "exists" xs p
  smt2 (PAll [] p) = smt2 p
  smt2 (PAll xs p) = smt2Quantifier "forall" xs p
  smt2 (PAtom r e1 e2) = mkRel r e1 e2
  smt2 (ELam b e) = smt2Lam b e
  smt2 (ECoerc t1 t2 e) = smt2Coerc t1 t2 e
  smt2 e = panic ("smtlib2 Pred  " ++ show e)

-- The nullary-family encoding currently covers free rank-1 constants.
-- Quantifying over polymorphic families needs a separate higher-rank model;
-- reject it explicitly instead of treating the family tag as its value.
withSmtBinders :: [(Symbol, Sort)] -> SymM a -> SymM a
withSmtBinders binders action
  | any (isPolyValueSort . snd) binders
  = panic "SMTLIB2: quantified polymorphic value families are not supported"
  | otherwise = withSmtShadowing (map fst binders) $ do
      modify (`insertsSymEnv` binders)
      action

-- Keep declarations discovered in the body, but restore lexical symbol
-- information. SMT let/define-fun arguments are already monomorphic here.
withSmtShadowing :: [Symbol] -> SymM a -> SymM a
withSmtShadowing names action = do
  previous <- get
  modify (\env -> (deletesSymEnv env names)
    { seTheory = foldr deleteSEnv (seTheory env) names })
  result <- action
  modify (\env -> env { seSort = seSort previous, seTheory = seTheory previous })
  pure result

smt2Quantifier :: Builder -> [(Symbol, Sort)] -> Expr -> SymM Builder
smt2Quantifier quantifier originalBinders body
  | null binders = smt2 body
  | otherwise = withSmtBinders binders $ do
      names <- smt2s binders
      predicate <- smt2 body
      pure $ parenSeqs [quantifier, parens names, predicate]
  where
    binders = retainQuantifiedBinders [body] originalBinders

-- Vacuous quantification does not change a predicate over LF's nonempty
-- logical domains. Apply that law only to otherwise unsupported family
-- binders; used families still require a separate quantified-family model.
-- Patterns count as uses and are interpreted in the same lexical scope.
retainQuantifiedBinders :: [Expr] -> [(Symbol, Sort)] -> [(Symbol, Sort)]
retainQuantifiedBinders expressions = filter retained
  where
    free = HS.unions (map exprSymbolsSet expressions)
    retained (name, sort) = not (isPolyValueSort sort) || HS.member name free

-- | smt2Cast uses the 'as x T' pattern needed for polymorphic ADT constructors
--   like Nil, see `tests/pos/adt_list_1.fq`

smt2Cast :: Expr -> Sort -> SymM Builder
smt2Cast (EVar x) t = smt2Var x t
smt2Cast e        _ = smt2    e

smt2Var :: Symbol -> Sort -> SymM Builder
smt2Var x t
  | isLamArgSymbol x = smtLamArg x t
  | otherwise        = do env <- get
                          case polyValueSort env x of
                            Just scheme -> smt2PolyValue x scheme t
                            Nothing -> case symEnvTheory x env of
                              Just theory
                                | tsInterp theory == Ctor
                                , isPolyInst (tsSort theory) t -> smt2VarAs x t
                              _ -> smt2 x

-- | A family identity and a logical instance ID select one value. Logical
-- instance identity survives SMT erasure, including nested function sorts.
-- Repeated occurrences select the same value; equality at one instance does
-- not equate family identities or values at other instances.
smt2PolyValue :: Symbol -> Sort -> Sort -> SymM Builder
smt2PolyValue x _ FAbs{} = unresolvedPolyValue x
smt2PolyValue x scheme t
  | not (all (`occursInSort` body) variables) = panic
      ("SMTLIB2: phantom type parameter in polymorphic value family "
        ++ showpp x ++ "; its instance cannot be recovered from the result sort")
  | otherwise = do
      instanceIndex <- valueInstanceIndex t
      applySymbol <- symbolAtName applyName (FFunc FInt t)
      valueTag <- smt2 x
      instanceTag <- smt2 instanceIndex
      pure $ parenSeqs [Builder.fromText applySymbol, valueTag, instanceTag]
  where
    (variables, body) = bkAbs scheme

occursInSort :: Int -> Sort -> Bool
occursInSort variable = go
  where
    go (FVar index) = index == variable
    go (FFunc argument result) = go argument || go result
    go (FApp constructor argument) = go constructor || go argument
    go (FAbs index body) = index /= variable && go body
    go _ = False

unresolvedPolyValue :: Symbol -> SymM a
unresolvedPolyValue x = panic
  ("SMTLIB2: uninstantiated polymorphic value family " ++ showpp x
    ++ "; expected an explicit monomorphic result sort")

smt2VarAs :: Symbol -> Sort -> SymM Builder
smt2VarAs x t =
  do s <- smt2 x
     s1 <- smt2SortMono x t
     pure $ parenSeqs ["as", s, s1]

-- the next four functions (ones containing a call to `symbolAtName`) can trigger
-- an expansion of the "nursery" tag table ('seApplsCur' in 'SymEnv') when processing
-- a fresh function sort
smtLamArg :: Symbol -> Sort -> SymM Builder
smtLamArg x t =
  do s <- symbolAtName x (FFunc t FInt)
     pure $ Builder.fromText s

smt2Lam :: (Symbol, Sort) -> Expr -> SymM Builder
smt2Lam (x, xT) full@(ECst _ eT) =
  withSmtBinders [(x, xT)] $ do
     x' <- smtLamArg x xT
     lambda <- symbolAtName lambdaName (FFunc xT eT)
     f <- smt2 full
     pure $ parenSeqs [Builder.fromText lambda, x', f]
smt2Lam _ e
  = panic ("smtlib2: Cannot serialize unsorted lambda: " ++ showpp e)

smt2App :: Expr -> SymM Builder
smt2App (EApp (EApp f e1) e2)
  | Just t <- unApplyAt f
  = do a <- symbolAtName applyName t
       s <- smt2s [e1, e2]
       pure $ parenSeqs [Builder.fromText a, s]
smt2App e = do s0 <- traverse smt2 es
               s1 <- Thy.smt2App smt2VarAs f s0
               case s1 of
                 Just b -> pure b
                 Nothing -> do s2 <- smt2 f
                               s3 <- smt2s es
                               pure $ parenSeqs [s2, s3]
  where
    (f, es) = splitEApp' e

smt2Coerc :: Sort -> Sort -> Expr -> SymM Builder
smt2Coerc t1 t2 e = do
  env <- get
  let s1 = Thy.sortSmtSort False (seData env) t1
      s2 = Thy.sortSmtSort False (seData env) t2
  if s1 == s2 then smt2 e
  else do
    coerceFn <- symbolAtName coerceName (FFunc t1 t2)
    s <- smt2 e
    pure $ parenSeqs [Builder.fromText coerceFn , s]

splitEApp' :: Expr -> (Expr, [Expr])
splitEApp'            = go []
  where
    go acc (EApp f e) = go (e:acc) f
  --   go acc (ECst e _) = go acc e
    go acc e          = (e, acc)

mkRel :: Brel -> Expr -> Expr -> SymM Builder
mkRel Ne  e1 e2 = mkNe e1 e2
mkRel Une e1 e2 = mkNe e1 e2
mkRel r   e1 e2 = do s <- smt2 r
                     s1 <- smt2 e1
                     s2 <- smt2 e2
                     pure $ parenSeqs [s, s1, s2]

mkNe :: Expr -> Expr -> SymM Builder
mkNe e1 e2 = do s1 <- smt2 e1
                s2 <- smt2 e2
                pure $ key "not" (parenSeqs ["=", s1, s2])
instance SMTLIB2 Command where
  smt2     (DeclData ds)       = do s <- smt2data ds
                                    pure $ key "declare-datatypes" s
  smt2     (Declare x ts t)    = do s <- smt2s ts
                                    s1 <- smt2 t
                                    pure $ parenSeqs ["declare-fun", Builder.fromText x, parens s, s1]
  smt2     c@(Define t)        = do s <- smt2SortMono c t
                                    pure $ key "declare-sort" s
  smt2     (DefineFunc name paramxs rsort e) =
    withSmtShadowing (map fst paramxs) $ do
       n <- smt2 name
       bParams <- traverse (\(s, t) -> do s0 <- smt2 s
                                          s1 <- smt2 t
                                          pure $ parenSeqs [s0 , s1]) paramxs
       r <- smt2 rsort
       e' <- smt2 e
       pure $ parenSeqs ["define-fun", n, parenSeqs bParams, r, e']

  smt2     (Assert Nothing p)  = {-# SCC "smt2-assert" #-}
                                  do s <- smt2 p
                                     pure $ key "assert" s
  smt2     (Assert (Just i) p) = {-# SCC "smt2-assert" #-}
                                  do s <- smt2 p
                                     pure $ key "assert" (parens ("!"<+> s <+> ":named p-" <> bShow i))
  smt2     (Distinct az)
    | length az < 2            = pure ""
    | otherwise                = do s <- smt2s az
                                    pure $ key "assert" $ key "distinct" s
  smt2     (AssertAx t)        = do s <- smt2 t
                                    pure $ key "assert" s
  smt2     Push                = pure "(push 1)"
  smt2     Pop                 = pure "(pop 1)"
  smt2     CheckSat            = pure "(check-sat)"
  smt2     (GetValue xs)       = do
    env <- get
    case [x | x <- xs, Just _ <- [polyValueSort env x]] of
      x : _ -> unresolvedPolyValue x
      [] -> do
        s <- smt2s xs
        pure $ key "key-value" (parens s)
  smt2     (CMany cmds)        = smt2s cmds
  smt2     Exit                = pure "(exit)"
  smt2     SetMbqi             = pure "(set-option :smt.mbqi true)"
  smt2     (Comment t)         = pure $ fromText ("; " <> t <> "\n")

instance SMTLIB2 (Triggered Expr) where
  smt2 (TR NoTrigger e)       = smt2 e
  smt2 (TR _ (PExist [] p))   = smt2 p
  smt2 t@(TR _ (PExist xs p)) = smtTr "exists" xs p t
  smt2 (TR _ (PAll   [] p))   = smt2 p
  smt2 t@(TR _ (PAll   xs p)) = smtTr "forall" xs p t
  smt2 (TR _ e)               = smt2 e

{-# INLINE smtTr #-}
smtTr :: Builder -> [(Symbol, Sort)] -> Expr -> Triggered Expr -> SymM Builder
smtTr q originalBinders p t
  | null binders = smt2 p
  | otherwise = withSmtBinders binders $ do
     s <- smt2s binders
     s1 <- smt2 p
     s2 <- smt2s patterns
     pure $ key q (parens s <+> key "!" (s1 <+> ":pattern" <> parens s2))
  where
    patterns = makeTriggers t
    binders = retainQuantifiedBinders (p : patterns) originalBinders

{-# INLINE smt2s #-}
smt2s :: SMTLIB2 a => [a] -> SymM Builder
smt2s as = smt2many <$> traverse smt2 as

{-# INLINE smt2many #-}
smt2many :: [Builder] -> Builder
smt2many = seqs
