module Language.Fixpoint.Horn.Transformations (
  poke,
  elim
) where

import           Language.Fixpoint.Horn.Types
import qualified Language.Fixpoint.Types      as F
import           Control.Monad (void)

-- $setup
-- >>> import Language.Fixpoint.Parse
-- >>> import Language.Fixpoint.Horn.Parse
-- >>> :set -XOverloadedStrings

-- |
-- >>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind01.smt2"
-- >>> qCstr (poke q)
-- (and (forall ((m int) (true)) (and (forall ((x1 int) (and (true) (x1 x1))) (and (forall ((v int) (v == m + 1)) ((v == x1))) (forall ((v int) (v == x1 + 1)) ((v == 2 + m))))) (exists ((x1 int) (and (true) (x1 x1))) ((true))))))
-- >>> (q, opts) <- parseFromFile hornP "tests/horn/pos/ebind02.smt2"
-- >>> qCstr (poke q)
-- (and (forall ((m int) (true)) (forall ((z int) (z == m - 1)) (and (forall ((v1 int) (v1 == z + 2)) ((k v1))) (and (forall ((x1 int) (and (true) (x1 x1))) (and (forall ((v2 int) (k v2)) ((v2 == x1))) (forall ((v3 int) (v3 == x1 + 1)) ((v3 == m + 2))))) (exists ((x1 int) (and (true) (x1 x1))) ((true))))))))

------------------------------------------------------------------------------
poke :: Query a -> Query ()
------------------------------------------------------------------------------
poke (Query quals vars cstr) = Query quals (map void vars ++ pivars) (pokec cstr)
  where pivars = ebs cstr

ebs :: Cstr a -> [Var ()]
ebs (Head _ _) = []
ebs (CAnd cs) = ebs =<< cs
ebs (All _ c) = ebs c
ebs (Any (Bind x t _) c) = HVar x [t] () : ebs c

pokec :: Cstr a -> Cstr ()
pokec (Head c _) = (Head c ())
pokec (CAnd c) = CAnd (pokec <$> c)
pokec (All b c2) = All b $ pokec c2
pokec (Any b c2) = CAnd [All b' $ pokec c2, Any b' (Head (Reft F.PTrue) ())]
  -- TODO: actually use the renamer?
  where
    Bind x t p = b
    b' = Bind x t (PAnd [p, pi])
    pi = Var x [x]

------------------------------------------------------------------------------
-- | elim solves all of the KVars in a Cstr (assuming no cycles...)
------------------------------------------------------------------------------
elim :: Cstr a -> Cstr a
------------------------------------------------------------------------------
elim c = foldl elim1 c (boundKvars c)

-- |
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test00.smt2"
-- (and (forall ((x int) (x > 0)) (forall ((y int) (y > x)) (forall ((v int) (v == x + y)) ((v > 0))))))
-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test01.smt2"
-- (and (forall ((x int) (x > 0)) (and (forall ((y int) (y > x)) (forall ((v int) (v == x + y)) ((v > 0)))) (forall ((z int) (z > 100)) (forall ((v int) (v == x + z)) ((v > 100)))))))

-- >>> elim . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- [("k0",["z"])]

-- Find a `sol1` solution to a kvar `k`, and then subsitute in the solution for
-- each rhs occurence of k.
elim1 :: Cstr a -> (F.Symbol,[F.Symbol]) -> Cstr a
elim1 c (k,su) = doelim k sol c
  where sol = sol1 (k,su) (scope k c)

-- scope drops extraneous leading binders so that we can take the strongest
-- scoped solution instead of the strongest solution
scope :: F.Symbol -> Cstr a -> Cstr a
scope k = go . snd . scope' k
  where go (All _ c') = go c'
        go c = c

-- |
-- >>> sc <- scope' "k0" . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- >>> sc
-- (True,(forall ((x int) (x > 0)) (and (forall ((y int) (y > x + 100)) (forall ((v int) (v == x + y)) ((k0 v)))) (forall ((z int) (k0 z)) (forall ((v int) (v == x + z)) ((v > 100)))))))

-- scope' prunes out branches that don't have k
scope' :: F.Symbol -> Cstr a -> (Bool, Cstr a)

scope' k (CAnd c) = case map snd $ filter fst $ map (scope' k) c of
                     []  -> (False, CAnd [])
                     [c] -> (True, c)
                     cs  -> (True, CAnd cs)

scope' k c@(All (Bind x t (Var k' su)) c')
  | k == k' = (True, c)
  | otherwise = All (Bind x t (Var k' su)) <$> scope' k c'
scope' k c@(All _ c')
  = const c <$> scope' k c'
scope' _ (Any _ _) = error "ebinds don't work with old elim"

scope' k c@(Head (Var k' _) _)
-- this case seems extraneous?
  | k == k'   = (True, c)
scope' _ c@Head{} = (False, c)

-- | A solution is a Hyp of binders (including one anonymous binder
-- that I've singled out here).
-- (What does Hyp stand for? Hypercube? but the dims don't line up...)
--
-- >>> c <- qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- >>> sol1 ("k0",["z"]) (scope "k0" c)
-- ([],POr [PAnd [PAtom Eq (EVar "z") (EVar "v")],POr []])

-- Naming conventions:
--  - `b` is a binder `forall . x:t .p =>`
--  - `bs` is a list of binders, or a "cube" that tracks all of the
--     information on the rhs of a given constraint
--  - `bss` is a Hyp, that tells us the solution to a Var, that is,
--     a collection of cubes that we'll want to disjunct

sol1 :: (F.Symbol, [F.Symbol]) -> Cstr a -> ([[Bind]], F.Expr)
sol1 k (CAnd cs) = (concat bsss, F.POr ps)
  where (bsss, ps) = unzip $ sol1 k <$> cs
sol1 k (All b c) = ((b:) <$> bss', c')
  where (bss', c') = sol1 k c
sol1 (k,xs) (Head (Var k' ys) _) | k == k'
  = ([], F.PAnd $ zipWith (F.PAtom F.Eq) (F.EVar <$> xs) (F.EVar <$> ys))
sol1 _ (Head _ _) = ([], F.PFalse)
sol1 _ (Any _ _) =  error "ebinds don't work with old elim"

-- |
-- >>> :add src/Language/Fixpoint/Horn/Parse.hs
-- >>> doParse' hCstrP "" "(forall ((v Int) (v = x + z)) ((v > 100)))"

doelim :: F.Symbol -> ([[Bind]], F.Expr) -> Cstr a -> Cstr a
doelim k bp (CAnd cs)
  = CAnd $ doelim k bp <$> cs
doelim k (bss, p) (All (Bind x t (Var k' _)) c)
  | k == k'
  = CAnd $ foldr All (All (Bind x t (Reft p)) $ doelim k (bss,p) c) <$> bss
doelim k bp (All b c)
  = All b (doelim k bp c)
doelim k _ (Head (Var k' _) a)
  | k == k'
  = Head (Reft F.PTrue) a
doelim _ _ (Head p a) = Head p a
doelim _ _ (Any _ _) =  error "ebinds don't work with old elim"

-- | Returns a list of KVars with thier arguments that are present as
-- binders in a given constraint
--
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/ebind01.smt2"
-- []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/ebind02.smt2"
-- [("k",["v2"])]
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test00.smt2"
-- []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test01.smt2"
-- []
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test02.smt2"
-- [("k0",["z"])]
--
-- TODO: fix the following
--
-- >>> boundKvars . qCstr . fst <$> parseFromFile hornP "tests/horn/pos/test03.smt2"
-- [("k0",["z"]), ... ]

boundKvars :: Cstr a -> [(F.Symbol,[F.Symbol])]
boundKvars (Head _ _) = []
boundKvars (CAnd c) = boundKvars =<< c
boundKvars (All (Bind _ _ (Var k xs)) c) = (k, xs) : boundKvars c
boundKvars (All _ c) = boundKvars c
boundKvars (Any (Bind _ _ (Var k xs)) c) = (k, xs) : boundKvars c
boundKvars (Any _ c) = boundKvars c