{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE OverloadedStrings         #-}

module Language.Fixpoint.Parse (

  -- * Top Level Class for Parseable Values
    Inputable (..)

  -- * Top Level Class for Parseable Values
  , Parser

  -- * Lexer to add new tokens
  -- , lexer -- TODO

  -- * Some Important keyword and parsers
  , reserved, reservedOp
  , parens  , brackets, angles, braces
  , semi    , comma
  , colon   , dcolon
  , dot
  , pairP
  , stringLiteral
  , spaces
  , spacesSameLine

  -- * Parsing basic entities

  --   fTyConP  -- Type constructors
  , lowerIdP    -- Lower-case identifiers
  , upperIdP    -- Upper-case identifiers
  , infixIdP    -- String Haskell infix Id
  , symbolP     -- Arbitrary Symbols
  , constantP   -- (Integer) Constants
  , natural     -- Non-negative integer
  , bindP       -- Binder (lowerIdP <* colon)
  , sortP       -- Sort
  , mkQual      -- constructing qualifiers
  , infixSymbolP -- parse infix symbols

  -- * Parsing recursive entities
  , exprP       -- Expressions
  , predP       -- Refinement Predicates
  , funAppP     -- Function Applications
  , qualifierP  -- Qualifiers
  , refaP       -- Refa
  , refP        -- (Sorted) Refinements
  , refDefP     -- (Sorted) Refinements with default binder
  , refBindP    -- (Sorted) Refinements with configurable sub-parsers
  , bvSortP     -- Bit-Vector Sort

  -- * Some Combinators
  , condIdP     --  condIdP  :: [Char] -> (Text -> Bool) -> Parser Text

  -- * Add a Location to a parsed value
  , locParserP
  , locLowerIdP
  , locUpperIdP

  -- * Getting a Fresh Integer while parsing
  , freshIntP

  -- * Parsing Function
  , doParse'
  , parseFromFile
  , remainderP

  -- * Utilities
  , isSmall
  , isNotReserved

  , initPState, PState (..)

  , Fixity(..), Assoc(..), addOperatorP

  -- * For testing
  , expr0P
  , dataFieldP
  , dataCtorP
  , dataDeclP

  ) where

import           Control.Monad.Combinators.Expr
import qualified Data.IntMap.Strict          as IM
import qualified Data.HashMap.Strict         as M
import qualified Data.HashSet                as S
import           Data.List                   (foldl')
import           Data.List.NonEmpty          (NonEmpty(..))
import qualified Data.Text                   as T
import           Data.Maybe                  (fromJust, fromMaybe)
import           Data.Void
import           Text.Megaparsec             hiding (State, ParseError)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer  as L
-- import           Text.Parsec       hiding (State)
-- import           Text.Parsec.Expr
-- import qualified Text.Parsec.Token           as Token
-- import           Text.Printf                 (printf)
import           GHC.Generics                (Generic)

import qualified Data.Char                   as Char -- (isUpper, isLower)
import           Language.Fixpoint.Smt.Bitvector
import           Language.Fixpoint.Types.Errors
import qualified Language.Fixpoint.Misc      as Misc
import           Language.Fixpoint.Smt.Types
-- import           Language.Fixpoint.Types.Visitor   (foldSort, mapSort)
import           Language.Fixpoint.Types hiding    (mapSort)
import           Text.PrettyPrint.HughesPJ         (text, nest, vcat, (<+>))

import Control.Monad.State

-- For reference,
--
-- in *parsec*, the base monad transformer is
--
-- ParsecT s u m a
--
-- where
--
--   s   is the input stream type
--   u   is the user state type
--   m   is the underlying monad
--   a   is the return type
--
-- whereas in *megaparsec*, the base monad transformer is
--
-- ParsecT e s m a
--
-- where
--
--   e   is the custom data component for errors
--   s   is the input stream type
--   m   is the underlying monad
--   a   is the return type
--
-- The Liquid Haskell parser tracks state in 'PState', primarily
-- for operator fixities.
--
-- The old Liquid Haskell parser did not use parsec's "user state"
-- functionality for 'PState', but instead wrapped a state monad
-- in a parsec monad. We do the same thing for megaparsec.
--
-- However, user state was still used for an additional 'Integer'
-- as a unique supply. We incorporate this in the 'PState'.
--
-- Furthermore, we have to decide whether the state in the parser
-- should be "backtracking" or not. "Backtracking" state resets when
-- the parser backtracks, and thus only contains state modifications
-- performed by successful parses. On the other hand, non-backtracking
-- state would contain all modifications made during the parsing
-- process and allow us to observe unsuccessful attempts.
--
-- It turns out that:
--
-- - parsec's old built-in user state is backtracking
-- - using @StateT s (ParsecT ...)@ is backtracking
-- - using @ParsecT ... (StateT s ...)@ is non-backtracking
--
-- We want all our state to be non-backtracking.
--
-- NOTE that this is in deviation from what the old LH parser did,
-- but I think that was plainly wrong.

type Parser = StateT PState (Parsec Void String)

data PState = PState { fixityTable :: OpTable
                     , fixityOps   :: [Fixity]
                     , empList     :: Maybe Expr
                     , singList    :: Maybe (Expr -> Expr)
                     , supply      :: !Integer
                     }

--------------------------------------------------------------------

{-
emptyDef :: Monad m => Token.GenLanguageDef String a m
emptyDef    = Token.LanguageDef
               { Token.commentStart   = ""
               , Token.commentEnd     = ""
               , Token.commentLine    = ""
               , Token.nestedComments = True
               , Token.identStart     = lower <|> char '_'             -- letter <|> char '_'
               , Token.identLetter    = satisfy (`S.member` symChars)  -- alphaNum <|> oneOf "_"
               , Token.opStart        = Token.opLetter emptyDef
               , Token.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~'"
               , Token.reservedOpNames= []
               , Token.reservedNames  = []
               , Token.caseSensitive  = True
               }

languageDef :: Monad m => Token.GenLanguageDef String a m
languageDef =
  emptyDef { Token.commentStart    = "/* "
           , Token.commentEnd      = " */"
           , Token.commentLine     = "//"
           , Token.identStart      = lower <|> char '_'
           , Token.identLetter     = alphaNum <|> oneOf "_"
           , Token.reservedNames   = S.toList reservedNames
           , Token.reservedOpNames =          reservedOpNames
           }
-}

reservedNames :: S.HashSet String
reservedNames = S.fromList
  [ -- reserved words used in fixpoint
    "SAT"
  , "UNSAT"
  , "true"
  , "false"
  , "mod"
  , "data"
  , "Bexp"
  -- , "True"
  -- , "Int"
  , "import"
  , "if", "then", "else"
  , "func"
  , "autorewrite"
  , "rewrite"

  -- reserved words used in liquid haskell
  , "forall"
  , "coerce"
  , "exists"
  , "module"
  , "spec"
  , "where"
  , "decrease"
  , "lazyvar"
  , "LIQUID"
  , "lazy"
  , "local"
  , "assert"
  , "assume"
  , "automatic-instances"
  , "autosize"
  , "axiomatize"
  , "bound"
  , "class"
  , "data"
  , "define"
  , "defined"
  , "embed"
  , "expression"
  , "import"
  , "include"
  , "infix"
  , "infixl"
  , "infixr"
  , "inline"
  , "instance"
  , "invariant"
  , "measure"
  , "newtype"
  , "predicate"
  , "qualif"
  , "reflect"
  , "type"
  , "using"
  , "with"
  , "in"
  ]

-- TODO: This is currently unused.
--
-- The only place where this is used in the original parsec code is in the
-- Text.Parsec.Token.operator parser.
--
_reservedOpNames :: [String]
_reservedOpNames =
  [ "+", "-", "*", "/", "\\", ":"
  , "<", ">", "<=", ">=", "=", "!=" , "/="
  , "mod", "and", "or"
  --, "is"
  , "&&", "||"
  , "~", "=>", "==>", "<=>"
  , "->"
  , ":="
  , "&", "^", "<<", ">>", "--"
  , "?", "Bexp"
  , "'"
  , "_|_"
  , "|"
  , "<:"
  , "|-"
  , "::"
  , "."
  ]

{-
lexer :: Monad m => Token.GenTokenParser String u m
lexer = Token.makeTokenParser languageDef
-}

-- | Consumes a line comment.
lhLineComment :: Parser ()
lhLineComment =
  L.skipLineComment "//"

-- | Consumes a block comment.
lhBlockComment :: Parser ()
lhBlockComment =
  L.skipBlockComment "/*" "*/"

-- | Consumes all whitespace, including LH comments.
spaces :: Parser ()
spaces =
  L.space
    space1
    lhLineComment
    lhBlockComment

-- | Consumes all whitespace, including LH comments, but not newlines.
spacesSameLine :: Parser ()
spacesSameLine =
  L.space
    (void $ takeWhile1P (Just "white space on same line") (\ c -> Char.isSpace c && c /= '\n'))
    lhLineComment
    lhBlockComment

-- | Parser that consumes a single char within an identifier (not start of identifier).
identLetter :: Parser Char
identLetter =
  alphaNumChar <|> oneOf ("_" :: String)

-- | Parser that consumes a single char within an operator (not start of operator).
opLetter :: Parser Char
opLetter =
  oneOf (":!#$%&*+./<=>?@\\^|-~'" :: String)

-- | Parser that consumes the given reserved word.
--
-- The input token cannot be longer than the given name.
--
-- NOTE: we currently don't double-check that the reserved word is in the
-- list of reserved words.
--
reserved :: String -> Parser ()
reserved x =
  void $ L.lexeme spaces (try (string x <* notFollowedBy identLetter))

-- | Parser that consumes the given reserved operator.
--
-- The input token cannot be longer than the given name.
--
-- NOTE: we currently don't double-check that the reserved operator is in the
-- list of reserved operators.
--
reservedOp :: String -> Parser ()
reservedOp x =
  void $ L.lexeme spaces (try (string x <* notFollowedBy opLetter))

-- | Parser that consumes the given symbol.
--
-- The difference with 'reservedOp' is that the given symbol is seen
-- as a token of its own, so the next character that follows does not
-- matter.
--
-- symbol :: String -> Parser String
-- symbol x =
--   L.symbol spaces (string x)

parens, brackets, angles, braces :: Parser a -> Parser a
parens   = between (L.symbol spaces "(") (L.symbol spaces ")")
brackets = between (L.symbol spaces "[") (L.symbol spaces "]")
angles   = between (L.symbol spaces "<") (L.symbol spaces ">")
braces   = between (L.symbol spaces "{") (L.symbol spaces "}")

-- | 'sbraces' is a more space-liberal version of 'braces'.
-- It allows to parse arbitrary whitespace before the closing
-- brace, even if the argument parser would normally admit
-- none or only limited spaces.
--
sbraces :: Parser a -> Parser a
sbraces pp   = braces $ (spaces *> pp <* spaces)

semi, colon, comma, dot :: Parser String
semi  = L.symbol spaces ";"
colon = L.symbol spaces ":"
comma = L.symbol spaces ","
dot   = L.symbol spaces "."

-- | Parses a string literal as a lexeme. This is based on megaparsec's
-- 'charLiteral' parser, which claims to handle all the single-character
-- escapes defined by the Haskell grammar.
--
stringLiteral :: Parser String
stringLiteral =
  L.lexeme spaces
    (char '\"' *> manyTill L.charLiteral (char '\"'))

-- TODO: this should not be needed; we should use spaces instead (or in rare cases, spacesSameLine)
-- whiteSpace :: Parser ()
-- whiteSpace    = _ -- Token.whiteSpace    lexer

-- | Consumes a float literal lexeme.
double :: Parser Double
double = L.lexeme spaces L.float

-- identifier :: Parser String
-- identifier = Token.identifier lexer

-- TODO: the following should not be needed and be replaced with spacesSameLine
-- TODO:AZ: pretty sure there is already a whitespace eater in parsec,
-- blanks :: Parser String
-- blanks  = many (satisfy (`elem` [' ', '\t']))

-- | Consumes a natural number literal lexeme, which can be
-- in decimal, octal and hexadecimal representation.
--
natural :: Parser Integer
natural = L.lexeme spaces $
      try (char '0' *> char' 'x') *> L.hexadecimal
  <|> try (char '0' *> char' 'o') *> L.octal
  <|> L.decimal

-- TODO: It is totally unclear whether we need to also
-- parse signed integers. It seems the old 'integer'
-- parser could in fact only parse non-negative integers.

-- | Integer
-- integer :: Parser Integer
-- integer = _ -- Token.natural lexer <* spaces

--  try (char '-' >> (negate <$> posInteger))
--       <|> posInteger
-- posInteger :: Parser Integer
-- posInteger = toI <$> (many1 digit <* spaces)
--  where
--    toI :: String -> Integer
--    toI = read

----------------------------------------------------------------
------------------------- Expressions --------------------------
----------------------------------------------------------------

locParserP :: Parser a -> Parser (Located a)
locParserP p = do l1 <- getSourcePos
                  x  <- p
                  l2 <- getSourcePos
                  return $ Loc l1 l2 x


-- FIXME: we (LH) rely on this parser being dumb and *not* consuming trailing
-- whitespace, in order to avoid some parsers spanning multiple lines..

condIdP  :: Parser Char -> S.HashSet Char -> (String -> Bool) -> Parser Symbol
condIdP initP okChars p
  = do c    <- initP
       cs   <- takeWhileP Nothing (`S.member` okChars)
       spacesSameLine
       let s = c:cs
       guard (p s)
       pure (symbol s)

-- upperIdP :: Parser Symbol
-- upperIdP = do
--  c  <- upper
--  cs <- many (satisfy (`S.member` symChars))
--  blanks
--  return (symbol $ c:cs)
-- lowerIdP = do
  -- c  <- satisfy (\c -> isLower c || c == '_' )
  -- cs <- many (satisfy (`S.member` symChars))
  -- blanks
  -- return (symbol $ c:cs)

-- TODO:RJ we really _should_ just use the below, but we cannot,
-- because 'identifier' also chomps newlines which then make
-- it hard to parse stuff like: "measure foo :: a -> b \n foo x = y"
-- as the type parser thinks 'b \n foo` is a type. Sigh.
-- lowerIdP :: Parser Symbol
-- lowerIdP = symbol <$> (identifier <* blanks)

upperIdP :: Parser Symbol
upperIdP  = condIdP upperChar                  symChars (const True)

lowerIdP :: Parser Symbol
lowerIdP  = condIdP (lowerChar <|> char '_')   symChars isNotReserved

symCharsP :: Parser Symbol
symCharsP = condIdP (letterChar <|> char '_')  symChars isNotReserved

isNotReserved :: String -> Bool
isNotReserved s = not (s `S.member` reservedNames)

-- (&&&) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
-- f &&& g = \x -> f x && g x
-- | String Haskell infix Id
infixIdP :: Parser String
infixIdP = many (satisfy (`notElem` [' ', '.']))

isSmall :: Char -> Bool
isSmall c = Char.isLower c || c == '_'

locSymbolP, locLowerIdP, locUpperIdP :: Parser LocSymbol
locLowerIdP = locParserP lowerIdP
locUpperIdP = locParserP upperIdP
locSymbolP  = locParserP symbolP

-- | Arbitrary Symbols
symbolP :: Parser Symbol
symbolP = symbol <$> symCharsP

-- | (Integer) Constants
constantP :: Parser Constant
constantP =  try (R <$> double)
         <|> I <$> natural


symconstP :: Parser SymConst
symconstP = SL . T.pack <$> stringLiteral

expr0P :: Parser Expr
expr0P
  =  trueP
 <|> falseP
 <|> fastIfP EIte exprP
 <|> coerceP exprP
 <|> (ESym <$> symconstP)
 <|> (ECon <$> constantP)
 <|> (reservedOp "_|_" >> return EBot)
 <|> lamP
 <|> try tupleP
  -- TODO:AZ get rid of these try, after the rest
 <|> try (parens exprP)
 <|> (reserved "[]" >> emptyListP)
 <|> try (brackets exprP >>= singletonListP)
 <|> try (parens exprCastP)
 <|> (charsExpr <$> symCharsP)

emptyListP :: Parser Expr
emptyListP = do
  e <- empList <$> get
  case e of
    Nothing -> fail "No parsing support for empty lists"
    Just s  -> return s

singletonListP :: Expr -> Parser Expr
singletonListP e = do
  f <- singList <$> get
  case f of
    Nothing -> fail "No parsing support for singleton lists"
    Just s  -> return $ s e

exprCastP :: Parser Expr
exprCastP
  = do e  <- exprP
       (try dcolon) <|> colon
       so <- sortP
       return $ ECst e so

charsExpr :: Symbol -> Expr
charsExpr cs
  | isSmall (headSym cs) = expr cs
  | otherwise            = EVar cs

fastIfP :: (Expr -> a -> a -> a) -> Parser a -> Parser a
fastIfP f bodyP
  = do reserved "if"
       p <- predP
       reserved "then"
       b1 <- bodyP
       reserved "else"
       b2 <- bodyP
       return $ f p b1 b2

coerceP :: Parser Expr -> Parser Expr
coerceP p = do
  reserved "coerce"
  (s, t) <- parens (pairP sortP (reservedOp "~") sortP)
  e      <- p
  return $ ECoerc s t e



{-
qmIfP f bodyP
  = parens $ do
      p  <- predP
      reserved "?"
      b1 <- bodyP
      colon
      b2 <- bodyP
      return $ f p b1 b2
-}

-- | Used as input to @Text.Parsec.Expr.buildExpressionParser@ to create @exprP@
expr1P :: Parser Expr
expr1P
  =  try funAppP
 <|> expr0P

-- | Expressions
exprP :: Parser Expr
exprP =
  do
    table <- gets fixityTable
    makeExprParser expr1P (flattenOpTable table)

data Assoc = AssocNone | AssocLeft | AssocRight

data Fixity
  = FInfix   {fpred :: Maybe Int, fname :: String, fop2 :: Maybe (Expr -> Expr -> Expr), fassoc :: Assoc}
  | FPrefix  {fpred :: Maybe Int, fname :: String, fop1 :: Maybe (Expr -> Expr)}
  | FPostfix {fpred :: Maybe Int, fname :: String, fop1 :: Maybe (Expr -> Expr)}


-- | An OpTable stores operators by their fixity.
--
-- Fixity levels range from 9 (highest) to 0 (lowest).
type OpTable = IM.IntMap [Operator Parser Expr] -- [[Operator Parser Expr]]

-- | Transform an operator table to the form expected by 'makeExprParser',
-- which wants operators sorted by decreasing priority.
--
flattenOpTable :: OpTable -> [[Operator Parser Expr]]
flattenOpTable =
  (snd <$>) <$> IM.toDescList

-- | Add an operator to the parsing state.
addOperatorP :: Fixity -> Parser ()
addOperatorP op
  = modify $ \s -> s{ fixityTable = addOperator op (fixityTable s)
                    , fixityOps   = op:fixityOps s
                    }

infixSymbolP :: Parser Symbol
infixSymbolP = do
  ops <- infixOps <$> get
  choice (reserved' <$> ops)
  where
    infixOps st = [s | FInfix _ s _ _ <- fixityOps st]
    reserved' x = reserved x >> return (symbol x)

-- | Helper function that turns an associativity into the right constructor for 'Operator'.
mkInfix :: Assoc -> parser (expr -> expr -> expr) -> Operator parser expr
mkInfix AssocLeft  = InfixL
mkInfix AssocRight = InfixR
mkInfix AssocNone  = InfixN

-- | Add the given operator to the operator table.
addOperator :: Fixity -> OpTable -> OpTable
addOperator (FInfix p x f assoc) ops
 = insertOperator (makePrec p) (mkInfix assoc (reservedOp x >> return (makeInfixFun x f))) ops
addOperator (FPrefix p x f) ops
 = insertOperator (makePrec p) (Prefix (reservedOp x >> return (makePrefixFun x f))) ops
addOperator (FPostfix p x f) ops
 = insertOperator (makePrec p) (Postfix (reservedOp x >> return (makePrefixFun x f))) ops

-- | Helper function for computing the priority of an operator.
--
-- If no explicit priority is given, a priority of 9 is assumed.
--
makePrec :: Maybe Int -> Int
makePrec = fromMaybe 9

makeInfixFun :: String -> Maybe (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
makeInfixFun x = fromMaybe (\e1 e2 -> EApp (EApp (EVar $ symbol x) e1) e2)

makePrefixFun :: String -> Maybe (Expr -> Expr) -> Expr -> Expr
makePrefixFun x = fromMaybe (EApp (EVar $ symbol x))

-- | Add an operator at the given priority to the operator table.
insertOperator :: Int -> Operator Parser Expr -> OpTable -> OpTable
insertOperator i op = IM.alter (Just . (op :) . fromMaybe []) i

-- | The initial (empty) operator table.
initOpTable :: OpTable
initOpTable = IM.empty

-- | Built-in operator table, parameterised over the composition function.
bops :: Maybe Expr -> OpTable
bops cmpFun = foldl' (flip addOperator) initOpTable builtinOps
  where
    -- Built-in Haskell operators, see https://www.haskell.org/onlinereport/decls.html#fixity
    builtinOps :: [Fixity]
    builtinOps = [ FPrefix (Just 9) "-"   (Just ENeg)
                 , FInfix  (Just 7) "*"   (Just $ EBin Times) AssocLeft
                 , FInfix  (Just 7) "/"   (Just $ EBin Div)   AssocLeft
                 , FInfix  (Just 6) "-"   (Just $ EBin Minus) AssocLeft
                 , FInfix  (Just 6) "+"   (Just $ EBin Plus)  AssocLeft
                 , FInfix  (Just 5) "mod" (Just $ EBin Mod)   AssocLeft -- Haskell gives mod 7
                 , FInfix  (Just 9) "."   applyCompose        AssocRight
                 ]
    applyCompose :: Maybe (Expr -> Expr -> Expr)
    applyCompose = (\f x y -> (f `eApps` [x,y])) <$> cmpFun

-- | Function Applications
funAppP :: Parser Expr
funAppP            =  litP <|> exprFunP <|> simpleAppP
  where
    exprFunP = mkEApp <$> funSymbolP <*> funRhsP
    funRhsP  =  sepBy1 expr0P spacesSameLine
            <|> parens innerP
    innerP   = brackets (sepBy exprP semi)

    -- TODO:AZ the parens here should be superfluous, but it hits an infinite loop if removed
    simpleAppP     = EApp <$> parens exprP <*> parens exprP
    funSymbolP     = locParserP symbolP


tupleP :: Parser Expr
tupleP = do
  let tp = parens (pairP exprP comma (sepBy1 exprP comma))
  Loc l1 l2 (first, rest) <- locParserP tp
  let cons = symbol $ "(" ++ replicate (length rest) ',' ++ ")"
  return $ mkEApp (Loc l1 l2 cons) (first : rest)


-- TODO:AZ: The comment says BitVector literal, but it accepts any @Sort@
-- | BitVector literal: lit "#x00000001" (BitVec (Size32 obj))
litP :: Parser Expr
litP = do reserved "lit"
          l <- stringLiteral
          t <- sortP
          return $ ECon $ L (T.pack l) t

-- parenBrackets :: Parser a -> Parser a
-- parenBrackets  = parens . brackets

-- eMinus     = EBin Minus (expr (0 :: Integer))
-- eCons x xs = EApp (dummyLoc consName) [x, xs]
-- eNil       = EVar nilName

lamP :: Parser Expr
lamP
  = do reservedOp "\\"
       x <- symbolP
       colon
       t <- sortP
       reservedOp "->"
       e  <- exprP
       return $ ELam (x, t) e

dcolon :: Parser String
dcolon = string "::" <* spaces

varSortP :: Parser Sort
varSortP  = FVar  <$> parens intP

funcSortP :: Parser Sort
funcSortP = parens $ mkFFunc <$> intP <* comma <*> sortsP

sortsP :: Parser [Sort]
sortsP = brackets $ sepBy sortP semi

-- | Sort
sortP    :: Parser Sort
sortP    = sortP' (sepBy sortArgP spacesSameLine)

sortArgP :: Parser Sort
sortArgP = sortP' (return [])

{-
sortFunP :: Parser Sort
sortFunP
   =  try (string "@" >> varSortP)
  <|> (fTyconSort <$> fTyConP)
-}

sortP' :: Parser [Sort] -> Parser Sort
sortP' appArgsP
   =  parens sortP
  <|> (reserved "func" >> funcSortP)
  <|> (fAppTC listFTyCon . pure <$> brackets sortP)
  <|> bvSortP
  <|> (fAppTC <$> fTyConP <*> appArgsP)
  <|> (fApp   <$> tvarP   <*> appArgsP)

tvarP :: Parser Sort
tvarP
   =  (string "@" >> varSortP)
  <|> (FObj . symbol <$> lowerIdP)


fTyConP :: Parser FTycon
fTyConP
  =   (reserved "int"     >> return intFTyCon)
  <|> (reserved "Integer" >> return intFTyCon)
  <|> (reserved "Int"     >> return intFTyCon)
  -- <|> (reserved "int"     >> return intFTyCon) -- TODO:AZ duplicate?
  <|> (reserved "real"    >> return realFTyCon)
  <|> (reserved "bool"    >> return boolFTyCon)
  <|> (reserved "num"     >> return numFTyCon)
  <|> (reserved "Str"     >> return strFTyCon)
  <|> (symbolFTycon      <$> locUpperIdP)

-- | Bit-Vector Sort
bvSortP :: Parser Sort
bvSortP = mkSort <$> (bvSizeP "Size32" S32 <|> bvSizeP "Size64" S64)
  where
    bvSizeP ss s = do
      parens (reserved "BitVec" >> reserved ss)
      return s


--------------------------------------------------------------------------------
-- | Predicates ----------------------------------------------------------------
--------------------------------------------------------------------------------

pred0P :: Parser Expr
pred0P =  trueP
      <|> falseP
      <|> (reservedOp "??" >> makeUniquePGrad)
      <|> kvarPredP
      <|> (fastIfP pIte predP)
      <|> try predrP
      <|> (parens predP)
      <|> (reservedOp "?" *> exprP)
      <|> try funAppP
      <|> (eVar <$> symbolP)
      <|> (reservedOp "&&" >> pGAnds <$> predsP)
      <|> (reservedOp "||" >> POr  <$> predsP)

makeUniquePGrad :: Parser Expr
makeUniquePGrad
  = do uniquePos <- getSourcePos
       return $ PGrad (KV $ symbol $ show uniquePos) mempty (srcGradInfo uniquePos) mempty

-- qmP    = reserved "?" <|> reserved "Bexp"

trueP, falseP :: Parser Expr
trueP  = reserved "true"  >> return PTrue
falseP = reserved "false" >> return PFalse

kvarPredP :: Parser Expr
kvarPredP = PKVar <$> kvarP <*> substP

kvarP :: Parser KVar
kvarP = KV <$> (char '$' *> symbolP <* spaces)

substP :: Parser Subst
substP = mkSubst <$> many (brackets $ pairP symbolP aP exprP)
  where
    aP = reservedOp ":="

predsP :: Parser [Expr]
predsP = brackets $ sepBy predP semi

predP  :: Parser Expr
predP  = makeExprParser pred0P lops
  where
    lops = [ [Prefix (reservedOp "~"    >> return PNot)]
           , [Prefix (reservedOp "not " >> return PNot)]
           , [InfixR (reservedOp "&&"   >> return pGAnd)]
           , [InfixR (reservedOp "||"   >> return (\x y -> POr  [x,y]))]
           , [InfixR (reservedOp "=>"   >> return PImp)]
           , [InfixR (reservedOp "==>"  >> return PImp)]
           , [InfixR (reservedOp "<=>"  >> return PIff)]]

predrP :: Parser Expr
predrP = do e1    <- exprP
            r     <- brelP
            e2    <- exprP
            return $ r e1 e2

brelP ::  Parser (Expr -> Expr -> Expr)
brelP =  (reservedOp "==" >> return (PAtom Eq))
     <|> (reservedOp "="  >> return (PAtom Eq))
     <|> (reservedOp "~~" >> return (PAtom Ueq))
     <|> (reservedOp "!=" >> return (PAtom Ne))
     <|> (reservedOp "/=" >> return (PAtom Ne))
     <|> (reservedOp "!~" >> return (PAtom Une))
     <|> (reservedOp "<"  >> return (PAtom Lt))
     <|> (reservedOp "<=" >> return (PAtom Le))
     <|> (reservedOp ">"  >> return (PAtom Gt))
     <|> (reservedOp ">=" >> return (PAtom Ge))

--------------------------------------------------------------------------------
-- | BareTypes -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Refa
refaP :: Parser Expr
refaP =  try (pAnd <$> brackets (sepBy predP semi))
     <|> predP


-- | (Sorted) Refinements with configurable sub-parsers
refBindP :: Parser Symbol -> Parser Expr -> Parser (Reft -> a) -> Parser a
refBindP bp rp kindP
  = braces $ do
      x  <- bp
      t  <- kindP
      reservedOp "|"
      ra <- rp <* spaces
      return $ t (Reft (x, ra))


-- bindP      = symbol    <$> (lowerIdP <* colon)
-- | Binder (lowerIdP <* colon)
bindP :: Parser Symbol
bindP = symbolP <* colon

optBindP :: Symbol -> Parser Symbol
optBindP x = try bindP <|> return x

-- | (Sorted) Refinements
refP :: Parser (Reft -> a) -> Parser a
refP       = refBindP bindP refaP

-- | (Sorted) Refinements with default binder
refDefP :: Symbol -> Parser Expr -> Parser (Reft -> a) -> Parser a
refDefP x  = refBindP (optBindP x)

--------------------------------------------------------------------------------
-- | Parsing Data Declarations -------------------------------------------------
--------------------------------------------------------------------------------

dataFieldP :: Parser DataField
dataFieldP = DField <$> locSymbolP <* colon <*> sortP

dataCtorP :: Parser DataCtor
dataCtorP  = DCtor <$> locSymbolP
                   <*> braces (sepBy dataFieldP comma)

dataDeclP :: Parser DataDecl
dataDeclP  = DDecl <$> fTyConP <*> intP <* reservedOp "="
                   <*> brackets (many (reservedOp "|" *> dataCtorP))

--------------------------------------------------------------------------------
-- | Parsing Qualifiers --------------------------------------------------------
--------------------------------------------------------------------------------

-- | Qualifiers
qualifierP :: Parser Sort -> Parser Qualifier
qualifierP tP = do
  pos    <- getSourcePos
  n      <- upperIdP
  params <- parens $ sepBy1 (qualParamP tP) comma
  _      <- colon
  body   <- predP
  return  $ mkQual n params body pos

qualParamP :: Parser Sort -> Parser QualParam
qualParamP tP = do
  x     <- symbolP
  pat   <- qualPatP
  _     <- colon
  t     <- tP
  return $ QP x pat t

qualPatP :: Parser QualPattern
qualPatP
   =  (reserved "as" >> qualStrPatP)
  <|> return PatNone

qualStrPatP :: Parser QualPattern
qualStrPatP
   = (PatExact <$> symbolP)
  <|> parens (    (uncurry PatPrefix <$> pairP symbolP dot qpVarP)
              <|> (uncurry PatSuffix <$> pairP qpVarP  dot symbolP) )


qpVarP :: Parser Int
qpVarP = char '$' *> intP

symBindP :: Parser a -> Parser (Symbol, a)
symBindP = pairP symbolP colon

pairP :: Parser a -> Parser z -> Parser b -> Parser (a, b)
pairP xP sepP yP = (,) <$> xP <* sepP <*> yP

---------------------------------------------------------------------
-- | Axioms for Symbolic Evaluation ---------------------------------
---------------------------------------------------------------------

autoRewriteP :: Parser AutoRewrite
autoRewriteP = do
  args       <- sepBy sortedReftP spaces
  _          <- spaces
  _          <- reserved "="
  _          <- spaces
  (lhs, rhs) <- braces $
      pairP exprP (reserved "=") exprP
  return $ AutoRewrite args lhs rhs


defineP :: Parser Equation
defineP = do
  name   <- symbolP
  params <- parens        $ sepBy (symBindP sortP) comma
  sort   <- colon        *> sortP
  body   <- reserved "=" *> sbraces (
              if sort == boolSort then predP else exprP
               )
  return  $ mkEquation name params body sort

matchP :: Parser Rewrite
matchP = SMeasure <$> symbolP <*> symbolP <*> many symbolP <*> (reserved "=" >> exprP)

pairsP :: Parser a -> Parser b -> Parser [(a, b)]
pairsP aP bP = brackets $ sepBy1 (pairP aP (reserved ":") bP) semi
---------------------------------------------------------------------
-- | Parsing Constraints (.fq files) --------------------------------
---------------------------------------------------------------------

-- Entities in Query File
data Def a
  = Srt !Sort
  | Cst !(SubC a)
  | Wfc !(WfC a)
  | Con !Symbol !Sort
  | Dis !Symbol !Sort
  | Qul !Qualifier
  | Kut !KVar
  | Pack !KVar !Int
  | IBind !Int !Symbol !SortedReft
  | EBind !Int !Symbol !Sort
  | Opt !String
  | Def !Equation
  | Mat !Rewrite
  | Expand ![(Int,Bool)]
  | Adt  !DataDecl
  | AutoRW !Int !AutoRewrite
  | RWMap ![(Int,Int)]
  deriving (Show, Generic)
  --  Sol of solbind
  --  Dep of FixConstraint.dep

fInfoOptP :: Parser (FInfoWithOpts ())
fInfoOptP = do ps <- many defP
               return $ FIO (defsFInfo ps) [s | Opt s <- ps]

fInfoP :: Parser (FInfo ())
fInfoP = defsFInfo <$> {-# SCC "many-defP" #-} many defP

defP :: Parser (Def ())
defP =  Srt   <$> (reserved "sort"         >> colon >> sortP)
    <|> Cst   <$> (reserved "constraint"   >> colon >> {-# SCC "subCP" #-} subCP)
    <|> Wfc   <$> (reserved "wf"           >> colon >> {-# SCC "wfCP"  #-} wfCP)
    <|> Con   <$> (reserved "constant"     >> symbolP) <*> (colon >> sortP)
    <|> Dis   <$> (reserved "distinct"     >> symbolP) <*> (colon >> sortP)
    <|> Pack  <$> (reserved "pack"         >> kvarP)   <*> (colon >> intP)
    <|> Qul   <$> (reserved "qualif"       >> qualifierP sortP)
    <|> Kut   <$> (reserved "cut"          >> kvarP)
    <|> EBind <$> (reserved "ebind"        >> intP) <*> symbolP <*> (colon >> braces sortP)
    <|> IBind <$> (reserved "bind"         >> intP) <*> symbolP <*> (colon >> sortedReftP)
    <|> Opt    <$> (reserved "fixpoint"    >> stringLiteral)
    <|> Def    <$> (reserved "define"      >> defineP)
    <|> Mat    <$> (reserved "match"       >> matchP)
    <|> Expand <$> (reserved "expand"      >> pairsP intP boolP)
    <|> Adt    <$> (reserved "data"        >> dataDeclP)
    <|> AutoRW <$> (reserved "autorewrite" >> intP) <*> autoRewriteP
    <|> RWMap  <$> (reserved "rewrite"     >> pairsP intP intP)


sortedReftP :: Parser SortedReft
sortedReftP = refP (RR <$> (sortP <* spaces))

wfCP :: Parser (WfC ())
wfCP = do reserved "env"
          env <- envP
          reserved "reft"
          r   <- sortedReftP
          let [w] = wfC env r ()
          return w

subCP :: Parser (SubC ())
subCP = do pos <- getSourcePos
           reserved "env"
           env <- envP
           reserved "lhs"
           lhs <- sortedReftP
           reserved "rhs"
           rhs <- sortedReftP
           reserved "id"
           i   <- natural <* spaces
           tag <- tagP
           pos' <- getSourcePos
           return $ subC' env lhs rhs i tag pos pos'

subC' :: IBindEnv
      -> SortedReft
      -> SortedReft
      -> Integer
      -> Tag
      -> SourcePos
      -> SourcePos
      -> SubC ()
subC' env lhs rhs i tag l l'
  = case cs of
      [c] -> c
      _   -> die $ err sp $ "RHS without single conjunct at" <+> pprint l'
    where
       cs = subC env lhs rhs (Just i) tag ()
       sp = SS l l'


tagP  :: Parser [Int]
tagP  = reserved "tag" >> spaces >> brackets (sepBy intP semi)

envP  :: Parser IBindEnv
envP  = do binds <- brackets $ sepBy (intP <* spaces) semi
           return $ insertsIBindEnv binds emptyIBindEnv

intP :: Parser Int
intP = fromInteger <$> natural

boolP :: Parser Bool
boolP = (reserved "True" >> return True)
    <|> (reserved "False" >> return False)

defsFInfo :: [Def a] -> FInfo a
defsFInfo defs = {-# SCC "defsFI" #-} FI cm ws bs ebs lts dts kts qs binfo adts mempty mempty ae
  where
    cm         = Misc.safeFromList
                   "defs-cm"        [(cid c, c)         | Cst c       <- defs]
    ws         = Misc.safeFromList
                   "defs-ws"        [(i, w)              | Wfc w    <- defs, let i = Misc.thd3 (wrft w)]
    bs         = bindEnvFromList  $ exBinds ++ [(n,x,r)  | IBind n x r <- defs]
    ebs        =                    [ n                  | (n,_,_) <- exBinds]
    exBinds    =                    [(n, x, RR t mempty) | EBind n x t <- defs]
    lts        = fromListSEnv       [(x, t)             | Con x t     <- defs]
    dts        = fromListSEnv       [(x, t)             | Dis x t     <- defs]
    kts        = KS $ S.fromList    [k                  | Kut k       <- defs]
    qs         =                    [q                  | Qul q       <- defs]
    binfo      = mempty
    expand     = M.fromList         [(fromIntegral i, f)| Expand fs   <- defs, (i,f) <- fs]
    eqs        =                    [e                  | Def e       <- defs]
    rews       =                    [r                  | Mat r       <- defs]
    autoRWs    = M.fromList         [(arId , s)         | AutoRW arId s <- defs]
    rwEntries  =                    [(i, f)             | RWMap fs   <- defs, (i,f) <- fs]
    rwMap      = foldl insert (M.fromList []) rwEntries
                 where
                   insert map (cid, arId) =
                     case M.lookup arId autoRWs of
                       Just rewrite ->
                         M.insertWith (++) (fromIntegral cid) [rewrite] map
                       Nothing ->
                         map
    cid        = fromJust . sid
    ae         = AEnv eqs rews expand rwMap
    adts       =                    [d                  | Adt d       <- defs]
    -- msg    = show $ "#Lits = " ++ (show $ length consts)

---------------------------------------------------------------------
-- | Interacting with Fixpoint --------------------------------------
---------------------------------------------------------------------

fixResultP :: Parser a -> Parser (FixResult a)
fixResultP pp
  =  (reserved "SAT"   >> return (Safe mempty))
 <|> (reserved "UNSAT" >> Unsafe <$> brackets (sepBy pp comma))
 <|> (reserved "CRASH" >> crashP pp)

crashP :: Parser a -> Parser (FixResult a)
crashP pp = do
  i   <- pp
  msg <- takeWhileP Nothing (const True) -- consume the rest of the input
  return $ Crash [i] msg

predSolP :: Parser Expr
predSolP = parens (predP  <* (comma >> iQualP))

iQualP :: Parser [Symbol]
iQualP = upperIdP >> parens (sepBy symbolP comma)

solution1P :: Parser (KVar, Expr)
solution1P = do
  reserved "solution:"
  k  <- kvP
  reservedOp ":="
  ps <- brackets $ sepBy predSolP semi
  return (k, simplify $ PAnd ps)
  where
    kvP = try kvarP <|> (KV <$> symbolP)

solutionP :: Parser (M.HashMap KVar Expr)
solutionP = M.fromList <$> sepBy solution1P spaces

solutionFileP :: Parser (FixResult Integer, M.HashMap KVar Expr)
solutionFileP = (,) <$> fixResultP natural <*> solutionP

--------------------------------------------------------------------------------

-- | Parse via the given parser, and obtain the rest of the input
-- as well as the final source position.
--
remainderP :: Parser a -> Parser (a, String, SourcePos)
remainderP p
  = do res <- p
       str <- getInput
       pos <- getSourcePos
       return (res, str, pos)

-- | Initial parser state.
initPState :: Maybe Expr -> PState
initPState cmpFun = PState { fixityTable = bops cmpFun
                           , empList     = Nothing
                           , singList    = Nothing
                           , fixityOps   = []
                           , supply      = 0
                           }

-- | Entry point for parsing, for testing.
--
-- Take the top-level parser, the source file name, and the input as a string.
-- Fails with an exception on a parse error.
--
doParse' :: Parser a -> SourceName -> String -> a
doParse' parser fileName input =
  case runParser (evalStateT (remainderP (spaces *> parser)) (initPState Nothing)) fileName input of
    Left (ParseErrorBundle errors posState) -> -- parse errors; we extract the first error from the error bundle
      let
        ((e, pos) :| _, _) = attachSourcePos errorOffset errors posState
      in
        die $ err (SS pos pos) (dErr e)
    Right (r, "", _) -> r -- successful parse with no remaining input
    Right (_, r, l) -> die $ err (SS l l) (dRem r)
  where
    dErr e = vcat [ "parseError"        <+> Misc.tshow e
                  , "when parsing from" <+> text fileName ]
    dRem r = vcat [ "doParse has leftover"
                  , nest 4 (text r)
                  , "when parsing from" <+> text fileName ]


-- errorSpan :: ParseError -> SrcSpan
-- errorSpan e = SS l l where l = errorPos e

parseFromFile :: Parser b -> SourceName -> IO b
parseFromFile p f = doParse' p f <$> readFile f

-- | Obtain a fresh integer during the parsing process.
freshIntP :: Parser Integer
freshIntP = do n <- gets supply
               modify (\ s -> s{supply = n + 1})
               return n

---------------------------------------------------------------------
-- Standalone SMTLIB2 commands --------------------------------------
---------------------------------------------------------------------
commandsP :: Parser [Command]
commandsP = sepBy commandP semi

commandP :: Parser Command
commandP
  =  (reserved "var"      >> cmdVarP)
 <|> (reserved "push"     >> return Push)
 <|> (reserved "pop"      >> return Pop)
 <|> (reserved "check"    >> return CheckSat)
 <|> (reserved "assert"   >> (Assert Nothing <$> predP))
 <|> (reserved "distinct" >> (Distinct <$> brackets (sepBy exprP comma)))

cmdVarP :: Parser Command
cmdVarP = error "UNIMPLEMENTED: cmdVarP"
-- do
  -- x <- bindP
  -- t <- sortP
  -- return $ Declare x [] t

---------------------------------------------------------------------
-- Bundling Parsers into a Typeclass --------------------------------
---------------------------------------------------------------------

class Inputable a where
  rr  :: String -> a
  rr' :: String -> String -> a
  rr' _ = rr
  rr    = rr' ""

instance Inputable Symbol where
  rr' = doParse' symbolP

instance Inputable Constant where
  rr' = doParse' constantP

instance Inputable Expr where
  rr' = doParse' exprP

instance Inputable (FixResult Integer) where
  rr' = doParse' $ fixResultP natural

instance Inputable (FixResult Integer, FixSolution) where
  rr' = doParse' solutionFileP

instance Inputable (FInfo ()) where
  rr' = {-# SCC "fInfoP" #-} doParse' fInfoP

instance Inputable (FInfoWithOpts ()) where
  rr' = {-# SCC "fInfoWithOptsP" #-} doParse' fInfoOptP

instance Inputable Command where
  rr' = doParse' commandP

instance Inputable [Command] where
  rr' = doParse' commandsP

{-
---------------------------------------------------------------
--------------------------- Testing ---------------------------
---------------------------------------------------------------

-- A few tricky predicates for parsing
-- myTest1 = "((((v >= 56320) && (v <= 57343)) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o ((i - o) - 1)))) && (((numchars a o (i - (o -1))) >= 0) && (((i - o) - 1) >= 0)))) && ((not (((v >= 56320) && (v <= 57343)))) => (((numchars a o ((i - o) + 1)) == (1 + (numchars a o (i - o)))) && ((numchars a o (i - o)) >= 0))))"
--
-- myTest2 = "len x = len y - 1"
-- myTest3 = "len x y z = len a b c - 1"
-- myTest4 = "len x y z = len a b (c - 1)"
-- myTest5 = "x >= -1"
-- myTest6 = "(bLength v) = if n > 0 then n else 0"
-- myTest7 = "(bLength v) = (if n > 0 then n else 0)"
-- myTest8 = "(bLength v) = (n > 0 ? n : 0)"


sa  = "0"
sb  = "x"
sc  = "(x0 + y0 + z0) "
sd  = "(x+ y * 1)"
se  = "_|_ "
sf  = "(1 + x + _|_)"
sg  = "f(x,y,z)"
sh  = "(f((x+1), (y * a * b - 1), _|_))"
si  = "(2 + f((x+1), (y * a * b - 1), _|_))"

s0  = "true"
s1  = "false"
s2  = "v > 0"
s3  = "(0 < v && v < 100)"
s4  = "(x < v && v < y+10 && v < z)"
s6  = "[(v > 0)]"
s6' = "x"
s7' = "(x <=> y)"
s8' = "(x <=> a = b)"
s9' = "(x <=> (a <= b && b < c))"

s7  = "{ v: Int | [(v > 0)] }"
s8  = "x:{ v: Int | v > 0 } -> {v : Int | v >= x}"
s9  = "v = x+y"
s10 = "{v: Int | v = x + y}"

s11 = "x:{v:Int | true } -> {v:Int | true }"
s12 = "y : {v:Int | true } -> {v:Int | v = x }"
s13 = "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
s14 = "x:{v:a  | true} -> y:{v:b | true } -> {v:a | (x < v && v < y) }"
s15 = "x:Int -> Bool"
s16 = "x:Int -> y:Int -> {v:Int | v = x + y}"
s17 = "a"
s18 = "x:a -> Bool"
s20 = "forall a . x:Int -> Bool"

s21 = "x:{v : GHC.Prim.Int# | true } -> {v : Int | true }"

r0  = (rr s0) :: Pred
r0' = (rr s0) :: [Refa]
r1  = (rr s1) :: [Refa]


e1, e2  :: Expr
e1  = rr "(k_1 + k_2)"
e2  = rr "k_1"

o1, o2, o3 :: FixResult Integer
o1  = rr "SAT "
o2  = rr "UNSAT [1, 2, 9,10]"
o3  = rr "UNSAT []"

-- sol1 = doParse solution1P "solution: k_5 := [0 <= VV_int]"
-- sol2 = doParse solution1P "solution: k_4 := [(0 <= VV_int)]"

b0, b1, b2, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 :: BareType
b0  = rr "Int"
b1  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
b2  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x - y}"
b4  = rr "forall a . x : a -> Bool"
b5  = rr "Int -> Int -> Int"
b6  = rr "(Int -> Int) -> Int"
b7  = rr "({v: Int | v > 10} -> Int) -> Int"
b8  = rr "(x:Int -> {v: Int | v > x}) -> {v: Int | v > 10}"
b9  = rr "x:Int -> {v: Int | v > x} -> {v: Int | v > 10}"
b10 = rr "[Int]"
b11 = rr "x:[Int] -> {v: Int | v > 10}"
b12 = rr "[Int] -> String"
b13 = rr "x:(Int, [Bool]) -> [(String, String)]"

-- b3 :: BareType
-- b3  = rr "x:Int -> y:Int -> {v:Bool | ((v is True) <=> x = y)}"

m1 = ["len :: [a] -> Int", "len (Nil) = 0", "len (Cons x xs) = 1 + len(xs)"]
m2 = ["tog :: LL a -> Int", "tog (Nil) = 100", "tog (Cons y ys) = 200"]

me1, me2 :: Measure.Measure BareType Symbol
me1 = (rr $ intercalate "\n" m1)
me2 = (rr $ intercalate "\n" m2)
-}
