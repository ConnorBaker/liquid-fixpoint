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

module Language.Fixpoint.Smt.Serialize (smt2SortMono, nativeFunctionAxioms, freshSmtSymbols) where

import           Control.Monad.State
import Control.Monad (forM, guard, replicateM, when)
import           Data.ByteString.Builder (Builder, intDec)
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Types.Visitor as Vis
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy

-- import           Data.Text.Format
import           Language.Fixpoint.Misc (errorstar)
import           Language.Fixpoint.Utils.Builder as Builder
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
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
    do
        env <- get
        smt2 (Thy.sortSmtSort poly env t)

smt2data :: [DataDecl] -> SymM Builder
smt2data = smt2data'

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
  smt2 Times  = pure $ fromText $ symbolText mulFuncName
  smt2 Div    = pure $ fromText $ symbolText divFuncName
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
    smt2 expression = do
        names <- lexicalNames [] [expression]
        smt2Expr names expression

-- Ordinary names start with "key$" and symbolAtName names with a letter.
-- Lexical names use "_lq_bound_" and the shared supply, so only raw SMT
-- fragments can collide, including with instances allocated later.
type LexicalNames = (SEnv Text, [Text])

lexicalNames :: [Symbol] -> [Expr] -> SymM LexicalNames
lexicalNames bound expressions = do
    environment <- get
    let spelling name = case symEnvTheory name environment of
            Just declaration | tsInterp declaration /= Uninterp -> [tsRaw declaration]
            _ -> []
        free = syms expressions `HS.difference` HS.fromList bound
        literalFolder = (Vis.defaultFolder :: Vis.Folder [Text] ()){Vis.accExpr = rawLiteral (seString environment) spelling}
        literals = foldMap (Vis.fold literalFolder () []) expressions
    pure (mempty, concatMap spelling (HS.toList free) ++ literals)
  where
    rawLiteral strings spelling _ (ESym constant) | not strings = spelling (symbol constant)
    rawLiteral _ _ _ (ECon (L raw sort)) | not (isString sort) = [raw]
    rawLiteral _ _ _ _ = []

-- Allocate ordinary identifiers from the same scoped supply as native value
-- instances and lexical binders. Reserve the complete support before allocation;
-- raw theory/literal fragments need the same conservative wire-name check.
freshSmtSymbols :: [Expr] -> Int -> SymM [Symbol]
freshSmtSymbols expressions count = do
    environment <- get
    (_, literals) <- lexicalNames [] expressions
    let occupied = syms expressions <> HS.fromList (map fst (toListSEnv (seSort environment) ++ toListSEnv (tsSort <$> seTheory environment)))
        raw = literals ++ map (tsRaw . snd) (toListSEnv (seTheory environment))
        available index = not (HS.member name occupied || any (symbolSmtText name `T.isInfixOf`) raw)
          where
            name = intSymbol "lq_candidate_value" index
    replicateM count (intSymbol "lq_candidate_value" <$> freshSmtIndex available)

-- Term binders live in this lexical map, not in seSort: they cannot redefine
-- a declaration's FObj coordinates or acquire a same-spelled theory meaning.
-- Function tags and deferred instances remain in the enclosing SMT state.
smt2Expr :: LexicalNames -> Expr -> SymM Builder
smt2Expr locals = go
  where
    go (ESym z) = smt2 z
    go (ECon c) = smt2 c
    go (EVar x) = case lookupSEnv x (fst locals) of
        Just name -> pure (fromText name)
        Nothing -> do
            environment <- get
            case polyValueSort environment x of
                Just _ -> unresolvedPolyValue x
                Nothing -> maybe (smt2 x) (smt2Var locals x) (symEnvSort x environment)
    go e@(EApp _ _) = smt2App locals e
    go (ENeg e) = key "-" <$> go e
    go (EBin o e1 e2) = do
        so <- smt2 o
        s1 <- go e1
        s2 <- go e2
        pure $ parenSeqs [so, s1, s2]
    go (ELet x e1 e2) = do
        rhs <- go e1
        (bindings, inside) <- lexicalBinders locals [(x, ())]
        body <- smt2Expr inside e2
        pure $ parenSeqs ["let", parens (seqs [parenSeqs [fromText name, rhs] | (name, ()) <- bindings]), body]
    go (EIte e1 e2 e3) = do
        s1 <- go e1
        s2 <- go e2
        s3 <- go e3
        pure $ parenSeqs ["ite", s1, s2, s3]
    go (ECst e t) = smt2Cast locals e t
    go PTrue = pure "true"
    go PFalse = pure "false"
    go (PAnd []) = pure "true"
    go (PAnd ps) = key "and" . smt2many <$> traverse go ps
    go (POr []) = pure "false"
    go (POr ps) = key "or" . smt2many <$> traverse go ps
    go (PNot p) = key "not" <$> go p
    go (PImp p q) = binary "=>" p q
    go (PIff p q) = binary "=" p q
    go (PExist [] p) = go p
    go (PExist xs p) = quantifier "exists" xs p
    go (PAll [] p) = go p
    go (PAll xs p) = quantifier "forall" xs p
    go (PAtom r e1 e2) = mkRel locals r e1 e2
    go (ELam b e) = rejectPolyBinders [b] >> smt2Lam locals b e
    go (ECoerc t1 t2 e) = smt2Coerc locals t1 t2 e
    go e = panic ("smtlib2 Pred  " ++ show e)

    binary operator p q = do
        s1 <- go p
        s2 <- go q
        pure $ parenSeqs [operator, s1, s2]
    quantifier operator original p = smt2Quantifier (const (pure locals)) (smt2Expr locals) operator original p []

-- Body and patterns share one lexical telescope. The caller supplies the
-- enclosing scope and the body renderer for the unused-binder case.
smt2Quantifier :: ([(Symbol, Sort)] -> SymM LexicalNames) -> (Expr -> SymM Builder) -> Builder -> [(Symbol, Sort)] -> Expr -> [[Expr]] -> SymM Builder
smt2Quantifier scope unbound operator original p patterns = do
    let bindings = retainQuantifiedBinders (p : concat patterns) original
    if null bindings
        then unbound p
        else do
            rejectPolyBinders bindings
            locals <- scope bindings
            (names, inside) <- lexicalBinders locals bindings
            telescope <- smt2Binders names
            body <- smt2Expr inside p
            rendered <- traverse (fmap smt2many . traverse (smt2Expr inside)) patterns
            let annotated
                    | null patterns = body
                    | otherwise = key "!" (seqs (body : [":pattern" <> parens pattern | pattern <- rendered]))
            pure $ parenSeqs [operator, parens telescope, annotated]

-- Logical domains are nonempty, so only unused, otherwise unsupported family
-- binders may be erased. Trigger patterns are uses in the same lexical scope.
retainQuantifiedBinders :: [Expr] -> [(Symbol, Sort)] -> [(Symbol, Sort)]
retainQuantifiedBinders expressions = filter retained
  where
    free = HS.unions (map exprSymbolsSet expressions)
    retained (name, sort) = not (isPolyValueSort sort) || HS.member name free

rejectPolyBinders :: [(Symbol, Sort)] -> SymM ()
rejectPolyBinders bindings =
    when (any (isPolyValueSort . snd) bindings) $
        panic "SMTLIB2: quantified polymorphic value families are not supported"

lexicalBinders :: LexicalNames -> [(Symbol, a)] -> SymM ([(Text, a)], LexicalNames)
lexicalBinders scope [] = pure ([], scope)
lexicalBinders (locals, raw) ((name, sort) : bindings) = do
    index <- freshSmtIndex (\i -> not (any (("_lq_bound_" <> T.pack (show i)) `T.isInfixOf`) raw))
    let fresh = "_lq_bound_" <> T.pack (show index)
    (rest, inside) <- lexicalBinders (insertSEnv name fresh locals, raw) bindings
    pure ((fresh, sort) : rest, inside)

smt2Binders :: [(Text, Sort)] -> SymM Builder
smt2Binders bindings = smt2many <$> traverse binder bindings
  where
    binder binding@(name, sort) = do
        carrier <- smt2SortMono binding sort
        pure $ parenSeqs [fromText name, carrier]

localHead :: LexicalNames -> Expr -> Bool
localHead locals (ECst expression _) = localHead locals expression
localHead locals (EVar name) = memberSEnv name (fst locals)
localHead _ _ = False

{- | smt2Cast uses the 'as x T' pattern needed for polymorphic ADT constructors
  like Nil, see `tests/pos/adt_list_1.fq`
-}
smt2Cast :: LexicalNames -> Expr -> Sort -> SymM Builder
smt2Cast locals (EVar x) t = maybe (smt2Var locals x t) (pure . fromText) (lookupSEnv x (fst locals))
smt2Cast locals e _ = smt2Expr locals e

smt2Var :: LexicalNames -> Symbol -> Sort -> SymM Builder
smt2Var locals x t
    | isLamArgSymbol x = smtLamArg x t
    | otherwise = do
        env <- get
        case Thy.isSmt2App (seTheory env) (EVar x) of
            Just arity | arity > 0 -> instanceValue
            _
                | Just scheme <- polyValueSort env x -> do
                    validatePolyValue x scheme t
                    instanceValue
                | otherwise -> ordinaryValue env
  where
    instanceValue = do
        index <- instantiatedValue locals x t
        pure $
            if index < 0
                then fromText (symbolSmtText (intSymbol "lq_instantiated_value" index))
                else fromText valueInstancePrefix <> intDec index
    ordinaryValue env = case symEnvSort x env of
        Just s | isPolyInst s t -> case symEnvTheory x env of
            Just declaration | tsInterp declaration == Ctor -> smt2VarAs x t
            Just declaration | tsInterp declaration == Uninterp -> instanceValue
            Nothing -> instanceValue
            _ -> smt2 x
        _ -> smt2 x

validatePolyValue :: Symbol -> Sort -> Sort -> SymM ()
validatePolyValue x scheme selected
    | FAbs{} <- selected = unresolvedPolyValue x
    | not (all (`HS.member` freeVariables) variables) =
        panic ("SMTLIB2: phantom type parameter in polymorphic value family " ++ showpp x)
    | Nothing <- normalizeValueInstance selected =
        panic ("SMTLIB2: higher-rank polymorphic value instance is not supported: " ++ showpp x)
    | otherwise = pure ()
  where
    (variables, body) = bkAbs scheme
    freeVariables = freeSortIndices body

unresolvedPolyValue :: Symbol -> SymM a
unresolvedPolyValue x = panic
    ("SMTLIB2: uninstantiated polymorphic value family " ++ showpp x
        ++ "; expected an explicit monomorphic result sort")

-- An ordinary polymorphic value is a family indexed by its selected logical
-- sort, not one SMT constant at the scheme's default Int instantiation. Native
-- callables require the same instance identity, with an apply equation below.
-- Decimal digits need no escaping; retain the canonical encoder for the prefix.
valueInstancePrefix :: Text
valueInstancePrefix = symbolSmtText (suffixSymbol "lq_instantiated_value" "")

instantiatedValue :: LexicalNames -> Symbol -> Sort -> SymM Int
instantiatedValue locals name selected = do
    env <- get
    let resolved = Vis.mapSort sourceAlias (resolveNumericSort (`lookupSEnv` seSort env) selected)
        sort = case polyValueSort env name of
            -- Canonical source aliases share a key, but unrelated nominal
            -- types retain their identity even when SMT gives them one carrier.
            Just _ ->
                maybe
                    (panic "SMTLIB2: higher-rank polymorphic value instance is not supported")
                    id
                    (normalizeValueInstance resolved)
            Nothing -> resolved
        instanceKey = ValueInstance name sort
        existing = lookupDeclarations instanceKey (seDeclarationsCur env : seDeclarations env)
    case existing of
        Just index -> pure index
        Nothing -> do
            -- Ordinary identifier encoding is injective; only raw SMT
            -- fragments and allocated names need the conservative scan.
            let globals =
                    map (tsRaw . snd) (toListSEnv (seTheory env))
                        ++ snd locals
                        ++ map snd (toListSEnv (fst locals))
                available index =
                    let candidate = intSymbol "lq_instantiated_value" index
                     in not (memberSEnv candidate (seSort env)) && all (not . T.isInfixOf (symbolSmtText candidate)) globals
            freshIndex <- freshSmtIndex available
            modify (\current -> current{seDeclarationsCur = HM.insert instanceKey freshIndex (seDeclarationsCur current)})
            pure freshIndex
  where
    sourceAlias (FApp (FTC constructor) element)
        | isListTC constructor && element == charSort = strSort
    sourceAlias (FTC constructor)
        | isListTC constructor = FTC listFTyCon
    sourceAlias source = source

-- Serializing these equations may request ordinary apply tags; the caller
-- declares the shared nursery before emitting the equations and their first use.
nativeFunctionAxioms :: SymM [Builder]
nativeFunctionAxioms = do
    env <- get
    forM
        [ (source, sort, tag, arity)
        | ((source, sort), tag) <- HM.toList (valueDeclarations (seDeclarationsCur env))
        , Just arity <- [Thy.isSmt2App (seTheory env) (EVar source)]
        , arity > 0
        ]
        $ \(source, sort, tag, arity) -> do
            let argumentNames = filter (`notElem` [source, tag]) (candidates "lq_native_argument")
                arguments = takeArguments arity sort argumentNames
                variables = [ECst (EVar name) domain | (name, domain, _) <- arguments]
                represented =
                    defuncEApp
                        env
                        (ECst (EVar tag) sort)
                        (zip variables [result | (_, _, result) <- arguments])
                native = case (tsRaw <$> symEnvTheory source env, variables, arguments) of
                    (Just "", function : values, _ : outputs) ->
                        defuncEApp env function (zip values [result | (_, _, result) <- outputs])
                    _ -> eApps (ECst (EVar source) sort) variables
                equation =
                    PAll
                        [(name, domain) | (name, domain, _) <- arguments]
                        (PAtom Eq represented native)
            smt2 (AssertAx (TR (Patterns [[represented]]) equation))
  where
    takeArguments 0 _ _ = []
    takeArguments n (FFunc domain result) (name : names) =
        (name, domain, result) : takeArguments (n - 1) result names
    takeArguments _ _ _ = panic "native function value lacks a resolved callable instance"

smt2VarAs :: Symbol -> Sort -> SymM Builder
smt2VarAs x t =
  do s <- smt2 x
     s1 <- smt2SortMono x t
     pure $ parenSeqs ["as", s, s1]

-- the next four functions (ones containing a call to `symbolAtName`) can trigger
-- an expansion of the "nursery" tag table ('seDeclarationsCur' in 'SymEnv') when processing
-- a fresh function sort
smtLamArg :: Symbol -> Sort -> SymM Builder
smtLamArg x t =
  do s <- symbolAtName x (FFunc t FInt)
     pure $ Builder.fromText s

smt2Lam :: LexicalNames -> (Symbol, Sort) -> Expr -> SymM Builder
smt2Lam locals (x, xT) full@(ECst _ eT) =
    do
        x' <- symbolAtName x (FFunc xT FInt)
        lambda <- symbolAtName lambdaName (FFunc xT eT)
        f <- smt2Expr (insertSEnv x x' (fst locals), snd locals) full
        pure $ parenSeqs [Builder.fromText lambda, fromText x', f]
smt2Lam _ _ e =
    panic ("smtlib2: Cannot serialize unsorted lambda: " ++ showpp e)

smt2App :: LexicalNames -> Expr -> SymM Builder
smt2App locals (EApp (EApp f e1) e2)
    | Just t <- unApplyAt f
    , not (localHead locals f) =
        do
            a <- symbolAtName applyName t
            s <- smt2many <$> traverse (smt2Expr locals) [e1, e2]
            pure $ parenSeqs [Builder.fromText a, s]
smt2App locals e = do
    environment <- get
    let native = do
            EVar name <- Just (dropECst f)
            guard (not (memberSEnv name (fst locals)))
            declaration <- symEnvTheory name environment
            guard (tsInterp declaration /= Uninterp)
            pure declaration
    arguments <- case (native, es) of
        (Just declaration, operator : indices)
            | tsInterp declaration == Theory
            , tsRaw declaration == "_"
            , EVar operation <- dropECst operator ->
                (:) <$> smt2 operation <*> traverse (smt2Expr locals) indices
        _ -> traverse (smt2Expr locals) es
    case native of
        Just declaration
            | ECst _ selected <- f -> pure (Thy.smt2App environment declaration selected arguments)
            | Just arity <- Thy.thyAppInfo declaration
            , length es >= arity ->
                pure (Thy.smt2App environment declaration (tsSort declaration) arguments)
        _ -> do
            function <- smt2Expr locals f
            pure $ parenSeqs [function, smt2many arguments]
  where
    (f, es) = splitEAppThroughECst e

smt2Coerc :: LexicalNames -> Sort -> Sort -> Expr -> SymM Builder
smt2Coerc locals t1 t2 e = do
    env <- get
    let s1 = Thy.sortSmtSort False env t1
        s2 = Thy.sortSmtSort False env t2
    if s1 == s2
        then smt2Expr locals e
        else do
            coerceFn <- symbolAtName coerceName (FFunc t1 t2)
            s <- smt2Expr locals e
            pure $ parenSeqs [Builder.fromText coerceFn, s]

mkRel :: LexicalNames -> Brel -> Expr -> Expr -> SymM Builder
mkRel locals Ne e1 e2 = mkNe locals e1 e2
mkRel locals Une e1 e2 = mkNe locals e1 e2
mkRel locals r e1 e2 = do
    s <- smt2 r
    s1 <- smt2Expr locals e1
    s2 <- smt2Expr locals e2
    pure $ parenSeqs [s, s1, s2]

mkNe :: LexicalNames -> Expr -> Expr -> SymM Builder
mkNe locals e1 e2 = do
    s1 <- smt2Expr locals e1
    s2 <- smt2Expr locals e2
    pure $ key "not" (parenSeqs ["=", s1, s2])
instance SMTLIB2 Command where
  smt2     (DeclData ds)       = do s <- smt2data ds
                                    pure $ key "declare-datatypes" s
  smt2     (Declare x ts t)    = do s <- smt2s ts
                                    s1 <- smt2 t
                                    pure $ parenSeqs ["declare-fun", Builder.fromText x, parens s, s1]
  smt2     c@(Define t)        = do s <- smt2SortMono c t
                                    pure $ key "declare-sort" s
  smt2 (DefineFunc name paramxs rsort e) = do
      n <- smt2 name
      scope <- lexicalNames (map fst paramxs) [e]
      (bindings, inside) <- lexicalBinders scope paramxs
      parameters <-
          traverse
              ( \(argument, sort) -> do
                  carrier <- smt2 sort
                  pure $ parenSeqs [fromText argument, carrier]
              )
              bindings
      r <- smt2 rsort
      e' <- smt2Expr inside e
      pure $ parenSeqs ["define-fun", n, parenSeqs parameters, r, e']

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
                                    environment <- get
                                    case filter (maybe False (const True) . polyValueSort environment) xs of
                                        x : _ -> unresolvedPolyValue x
                                        [] -> do
                                            s <- smt2s xs
                                            pure $ key "get-value" (parens s)
  smt2     (CMany cmds)        = smt2s cmds
  smt2     Exit                = pure "(exit)"
  smt2     SetMbqi             = pure "(set-option :smt.mbqi true)"
  smt2     (Comment t)         = pure $ fromText ("; " <> t <> "\n")

instance SMTLIB2 (Triggered Expr) where
    smt2 triggered =
        case triggered of
            TR (Patterns []) e -> smt2 e
            TR _ (PExist [] p) -> smt2 p
            t@(TR _ (PExist xs p)) -> smtTr "exists" xs p t
            TR _ (PAll [] p) -> smt2 p
            t@(TR _ (PAll xs p)) -> smtTr "forall" xs p t
            TR _ e -> smt2 e

{-# INLINE smtTr #-}
smtTr :: Builder -> [(Symbol, Sort)] -> Expr -> Triggered Expr -> SymM Builder
smtTr q xs p t = smt2Quantifier scope smt2 q xs p patterns
  where
    patterns = triggerPatterns t
    scope bindings = lexicalNames (map fst bindings) (p : concat patterns)

{-# INLINE smt2s #-}
smt2s :: SMTLIB2 a => [a] -> SymM Builder
smt2s as = smt2many <$> traverse smt2 as

{-# INLINE smt2many #-}
smt2many :: [Builder] -> Builder
smt2many = seqs
