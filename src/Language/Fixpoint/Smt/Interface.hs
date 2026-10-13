{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE DoAndIfThenElse           #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use isNothing" #-}

-- | This module contains an SMTLIB2 interface for
--   1. checking the validity, and,
--   2. computing satisfying assignments
--   for formulas.
--   By implementing a binary interface over the SMTLIB2 format defined at
--   http://www.smt-lib.org/
--   http://www.grammatech.com/resource/smt/SMTLIBTutorial.pdf

module Language.Fixpoint.Smt.Interface (

    -- * Commands
      Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)

    -- * Creating and killing SMTLIB2 Process
    , Context (..)
    , makeContext
    , makeContextNoLog
    , makeContextWithSEnv
    , cleanupContext

    -- * Execute Queries
    , command
    , smtSetMbqi

    -- * Query API
    , smtDecl
    , smtDecls
    , smtDefineFunc
    , smtAssert
    , smtFuncDecl
    , smtAssertAxiom
    , smtCheckUnsat
    , smtBracket, smtBracketAt
    , smtDistinct
    , smtPush, smtPop
    , smtComment

    -- * Check Validity
    , checkValid
    , checkValid'
    , checkValidWithContext
    , checkValids

    , funcSortVars

    ) where

import           Language.Fixpoint.Types.Config ( SMTSolver (..), solverFlags, elabSetBag
                                                , Config (solver, smtTimeout, smtMbqi, noStringTheory, save, saveDir, allowHO))
import qualified Language.Fixpoint.Misc          as Misc
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types         hiding (allowHO)
import qualified Language.Fixpoint.Types         as F
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Smt.Serialize (nativeFunctionAxioms)
import           Control.Applicative      ((<|>))
import           Control.Monad
import           Control.Monad.State
import           Control.Exception
import           Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as Char8
import           Data.Char
import qualified Data.HashMap.Strict      as M
import           Data.List                (uncons)
import           Data.Maybe              (fromMaybe)
import qualified Data.Text                as T
import qualified Data.Text.Encoding       as TE
import qualified Data.Text.IO
-- import           Data.Text.Format
import qualified Data.Text.Lazy.IO        as LTIO
import           System.Directory
import           Language.Fixpoint.Verbosity
import           System.FilePath
import           System.IO
import qualified Data.Attoparsec.Text     as A
-- import qualified Data.HashMap.Strict      as M
import           Data.Attoparsec.Internal.Types (Parser)
import           Text.PrettyPrint.HughesPJ (text)
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Utils.Builder as Builder
-- import qualified Language.Fixpoint.Types as F
-- import           Language.Fixpoint.Types.PrettyPrint (tracepp)
import qualified SMTLIB.Backends
import qualified SMTLIB.Backends.Process as Process
import qualified Language.Fixpoint.Conditional.Z3 as Conditional.Z3
import Control.Concurrent.Async (async)
import GHC.Stack (HasCallStack)

{-
runFile f
  = readFile f >>= runString

runString str
  = runCommands $ rr str

runCommands cmds
  = do me   <- makeContext Z3
       mapM_ (T.putStrLn . smt2) cmds
       zs   <- mapM (command me) cmds
       return zs
-}

checkValidWithContext ::
    (HasCallStack) => [(Symbol, Sort)] -> Expr -> Expr -> SmtM Bool
checkValidWithContext xts p q =
    smtBracket "checkValidWithContext" $
        checkValid' xts p q

{- | type ClosedPred E = {v:Pred | subset (vars v) (keys E) }
checkValid :: e:Env -> ClosedPred e -> ClosedPred e -> IO Bool
-}
checkValid ::
    (HasCallStack) =>
    Config -> FilePath -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValid cfg f xts p q = do
    (environment, [p', q']) <- validateSourceQuery cfg xts [p, q]
    bracket (makeContext cfg f) cleanupContext $ \me ->
        evalStateT (checkValid' xts p' q') me{ctxSymEnv = environment}

-- | Contextual queries consume already checked SMT expressions. Their caller
-- owns the live declarations and any preceding source elaboration.
checkValid' :: HasCallStack => [(Symbol, Sort)] -> Expr -> Expr -> SmtM Bool
checkValid' xts p q = do
  smtDecls xts
  smtAssert $ pAnd [p, PNot q]
  smtCheckUnsat

-- | If you already HAVE a context, where all the variables have declared types
--   (e.g. if you want to make MANY repeated Queries)

-- checkValid :: e:Env -> [ClosedPred e] -> IO [Bool]
checkValids :: Config -> FilePath -> [(Symbol, Sort)] -> [Expr] -> IO [Bool]
checkValids cfg f xts ps = do
    (environment, ps') <- validateSourceQuery cfg xts ps
    bracket (makeContext cfg f) cleanupContext $ \me ->
        evalStateT (checkValids' xts ps') me{ctxSymEnv = environment}

{- | Standalone validity queries own a complete source typing environment.
Check the original predicates together before Boolean simplification or
solver creation, then serialize that same judgment's typed numeric operators
and annotations. This does not run defunctionalization on source queries.
-}
validateSourceQuery :: Config -> [(Symbol, Sort)] -> [Expr] -> IO (SymEnv, [Expr])
validateSourceQuery cfg xts predicates = do
    PAnd elaborated <- evaluate $ elabExpr parameter (Just boolSort) (PAnd predicates)
    pure (environment, elaborated)
  where
    parameter = ElabParam (solverFlags cfg) "SMT validity query" environment
    -- The source judgment and serializer share the solver's native catalog.
    -- An explicitly declared ordinary symbol shadows its native namesake.
    native = foldr deleteSEnv (Thy.theorySymbols (solver cfg)) (map fst xts)
    environment = symEnv cfg (fromListSEnv xts <> fmap tsSort native) native [] mempty

checkValids' :: [(Symbol, Sort)] -> [Expr] -> SmtM [Bool]
checkValids' xts ps = do
    smtDecls xts
    forM ps $ \p ->
        smtBracket "checkValids" $
            smtAssert (PNot p) >> smtCheckUnsat

-- debugFile :: FilePath
-- debugFile = "DEBUG.smt2"

--------------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------------
--------------------------------------------------------------------------------

commandRaw :: Maybe Handle -> SMTLIB.Backends.Solver -> Bool -> Builder -> IO Response
commandRaw ctxLog ctxSolver ctxVerbose cmdBS = do
  resp <- SMTLIB.Backends.command ctxSolver cmdBS
  let respTxt =
        TE.decodeUtf8With (const $ const $ Just ' ') $
        LBS.toStrict resp
  case A.parseOnly responseP respTxt of
    Left e  -> Misc.errorstar $ "SMTREAD:" ++ e
    Right r -> do
      let textResponse = "; SMT Says: " <> T.pack (show r)
      forM_ ctxLog $ \h ->
        Data.Text.IO.hPutStrLn h textResponse
      when ctxVerbose $
        Data.Text.IO.putStrLn textResponse
      return r

--------------------------------------------------------------------------------
{-# SCC command #-}
command :: (HasCallStack) => Command -> SmtM Response
--------------------------------------------------------------------------------
command (CMany commands) = mapM_ command commands >> pure Ok
command !cmd = do
    -- whenLoud $ do LTIO.appendFile debugFile (s <> "\n")
    --               LTIO.putStrLn ("CMD-RAW:" <> s <> ":CMD-RAW:DONE")
    ctxLog <- gets ctxLog
    ctxSolver <- gets ctxSolver
    ctxVerbose <- gets ctxVerbose
    cmdBody <- liftSym $ runSmt2 cmd
    nativeAxioms <- liftSym nativeFunctionAxioms
    context <- get
    let environment = ctxSymEnv context
        declarations =
            [Declare name inputs result | (name, (inputs, result)) <- funcSortVars (ctxLams context) environment]
                ++ [Declare (symbolSmtText name) [] (sortSmtSort False environment sort) | ((_, sort), name) <- M.toList (valueDeclarations (seDeclarationsCur environment))]
    declarationBytes <- liftSym $ mapM runSmt2 declarations
    let cmdBS = mconcat [bytes <> "\n" | bytes <- declarationBytes ++ nativeAxioms] <> cmdBody
    modify $ \current ->
        current
            { ctxSymEnv =
                (ctxSymEnv current)
                    { seDeclarations = commitDeclarations (seDeclarationsCur environment) (seDeclarations environment)
                    , seDeclarationsCur = M.empty
                    }
            }
    requested <- case cmd of
        GetValue names -> forM names $ \name -> do
            wire <- liftSym $ runSmt2 name
            pure (symbol (TE.decodeUtf8 (LBS.toStrict (BS.toLazyByteString wire))), name)
        _ -> pure []
    forM_ ctxLog $ \h -> lift $ do
        BS.hPutBuilder h cmdBS
        LBS.hPutStr h "\n"
    response <- lift $ case cmd of
        CheckSat -> commandRaw ctxLog ctxSolver ctxVerbose cmdBS
        GetValue _ -> restoreValueNames requested <$> commandRaw ctxLog ctxSolver ctxVerbose cmdBS
        _ -> SMTLIB.Backends.command_ ctxSolver cmdBS >> return Ok
    case cmd of
        Push -> modify $ \current ->
            let env = ctxSymEnv current
             in current
                    { ctxSymEnv =
                        env
                            { seDeclarations = M.empty : seDeclarations env
                            }
                    , ctxIxs = seIx env : ctxIxs current
                    }
        Pop -> modify $ \current ->
            let env = ctxSymEnv current
                (index, rest) = fromMaybe (0, []) (uncons (ctxIxs current))
             in current
                    { ctxSymEnv =
                        env
                            { seDeclarations = drop 1 (seDeclarations env)
                            , seIx = index
                            }
                    , ctxIxs = rest
                    }
        _ -> pure ()
    pure response

-- Correlate this reply with this request, including aliases and repetitions.
-- Never interpret a wire prefix independently of the names actually queried.
restoreValueNames :: [(Symbol, Symbol)] -> Response -> Response
restoreValueNames requested (Values values) = either Misc.errorstar Values (restore requested values)
  where
    restore [] [] = Right []
    restore _ [] = Left "SMT get-value omitted requested identifiers"
    restore names ((wire, value) : rest) =
        case break ((== wire) . fst) names of
            (before, (_, name) : after) -> ((name, value) :) <$> restore (before ++ after) rest
            _ -> Left ("SMT get-value returned an unrequested identifier: " ++ show wire)
restoreValueNames _ response@Error{} = response
restoreValueNames _ response = Misc.errorstar ("Unexpected SMT get-value response: " ++ show response)

-- | Enable Z3's dynamic MBQI option. Other solvers use startup configuration.
smtSetMbqi :: SmtM ()
smtSetMbqi = interact' SetMbqi

type SmtParser a = Parser T.Text a

responseP :: SmtParser Response
responseP = {- SCC "responseP" -} A.char '(' *> sexpP
         <|> A.string "sat"     *> return Sat
         <|> A.string "unsat"   *> return Unsat
         <|> A.string "unknown" *> return Unknown
         <|> A.string "unsupported" *> return (Error "unsupported")

sexpP :: SmtParser Response
sexpP = {- SCC "sexpP" -} A.string "error" *> (Error <$> errorP)
     <|> Values <$> valuesP

errorP :: SmtParser T.Text
errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

valuesP :: SmtParser [(Symbol, T.Text)]
valuesP = A.many1' pairP <* A.skipSpace <* A.char ')'

pairP :: SmtParser (Symbol, T.Text)
pairP = {- SCC "pairP" -}
  do A.skipSpace
     _ <- A.char '('
     !x <- symbolP
     A.skipSpace
     !v <- valueP
     A.skipSpace
     _ <- A.char ')'
     return (x,v)

symbolP :: SmtParser Symbol
symbolP = {- SCC "symbolP" -} symbol . fst <$> A.match (quotedSymbolP <|> atomP)

valueP :: SmtParser T.Text
valueP = {- SCC "valueP" -} fst <$> A.match termP
  where
    -- Model values are SMT terms, not necessarily literals, even for Bool.
    -- Preserve their syntax; validity filtering interprets only literal false.
    termP = listP <|> quotedSymbolP <|> stringP <|> atomP
    listP = A.char '(' *> spacesP *> A.many' (termP <* spacesP) *> A.char ')' *> pure ()
    stringP = A.char '"' *> rest
      where
        rest = do
          _ <- A.takeTill (== '"')
          _ <- A.char '"'
          next <- A.peekChar
          if next == Just '"' then A.anyChar *> rest else pure ()
    spacesP = A.skipSpace *> A.many' (A.char ';' *> A.skipWhile (/= '\n') *> A.skipSpace) *> pure ()

quotedSymbolP :: SmtParser ()
quotedSymbolP = A.char '|' *> A.skipWhile (/= '|') *> A.char '|' *> pure ()

atomP :: SmtParser ()
atomP = A.takeWhile1 (\c -> not (isSpace c || c `elem` ("()\"|;" :: String))) *> pure ()

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext :: Config -> FilePath -> IO Context
--------------------------------------------------------------------------
makeContext cfg f
  = do checkMbqiFlag cfg
       mb_hLog <- if not (save cfg) then pure Nothing else do
           createDirectoryIfMissing True $ takeDirectory smtFile
           hLog <- openFile smtFile WriteMode
           hSetBuffering hLog $ BlockBuffering $ Just $ 1024 * 1024 * 64
           return $ Just hLog
       me   <- makeContext' cfg mb_hLog
       pre  <- smtPreamble cfg (solver cfg) me
       forM_ pre $ \line -> do
           SMTLIB.Backends.command_ (ctxSolver me) line
           forM_ mb_hLog $ \hLog -> do
               BS.hPutBuilder hLog line
               LBS.hPutStr hLog "\n"
       return me
    where
       smtFile = extFileNameR' (saveDir cfg) Smt2 f

makeContextWithSEnv :: Config -> FilePath -> SymEnv -> DefinedFuns -> IO Context
makeContextWithSEnv cfg f env defns = do
    ctx <- makeContext cfg f
    let ctx' = ctx{ctxSymEnv = env{seSetBag = elabSetBag (solverFlags cfg)}, ctxDefines = defns}
    execStateT declare ctx'

makeContextNoLog :: Config -> IO Context
makeContextNoLog cfg = do
  checkMbqiFlag cfg
  me  <- makeContext' cfg Nothing
  pre <- smtPreamble cfg (solver cfg) me
  mapM_ (SMTLIB.Backends.command_ (ctxSolver me)) pre
  return me

makeProcess
  :: Maybe Handle
  -> Process.Config
  -> IO (SMTLIB.Backends.Backend, IO ())
makeProcess ctxLog cfg
  = do handl@Process.Handle {hMaybeErr = Just hErr, ..} <- Process.new cfg
       case ctxLog of
         Nothing -> return ()
         Just hLog -> void $ async $ forever
           (do errTxt <- LTIO.hGetLine hErr
               LTIO.hPutStrLn hLog $ "OOPS, SMT solver error:" <> errTxt
           ) `catch` \ SomeException {} -> return ()
       let backend = Process.toBackend handl
       hSetBuffering hOut $ BlockBuffering $ Just $ 1024 * 1024 * 64
       hSetBuffering hIn $ BlockBuffering $ Just $ 1024 * 1024 * 64
       return (backend, Process.close handl)

makeContext' :: Config -> Maybe Handle -> IO Context
makeContext' cfg ctxLog
  = do let slv = solver cfg
       (backend, closeIO) <- case slv of
         Z3      ->
           {- "z3 -smt2 -in"                   -}
           {- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
           {- "z3 -smtc -in MBQI=false"        -}
           makeProcess ctxLog $ Process.defaultConfig
                             { Process.exe = "z3"
                             , Process.args = ["-smt2", "-in"] }
         Z3mem   -> Conditional.Z3.makeZ3
         Mathsat -> makeProcess ctxLog $ Process.defaultConfig
                             { Process.exe = "mathsat"
                             , Process.args = ["-input=smt2"] }
         Cvc4    -> makeProcess ctxLog $
                      Process.defaultConfig
                             { Process.exe = "cvc4"
                             , Process.args = ["-L", "smtlib2"] }
         Cvc5    -> makeProcess ctxLog $
                      Process.defaultConfig
                             { Process.exe = "cvc5"
                             , Process.args = ["-L", "smtlib2", "--arrays-exp"] }
       solver <- SMTLIB.Backends.initSolver SMTLIB.Backends.Queuing backend
       loud <- isLoud
       return Ctx { ctxSolver    = solver
                  , ctxElabF     = solverFlags cfg
                  , ctxClose     = closeIO
                  , ctxLog       = ctxLog
                  , ctxVerbose   = loud
                  , ctxSymEnv    = symEnv cfg mempty mempty [] mempty
                  , ctxIxs       = []
                  , ctxDefines   = mempty
                  -- This is a heurstic to avoid generating large sequences of unused `lam_arg` symbols
                  -- when there's no higher-order reasoning. It might require some tuning on larger codebases
                  -- if `unknown function/constant lam_arg$XXX` errors are encountered.
                  , ctxLams      = allowHO cfg
                  , config       = cfg
                  }

-- | Close file handles and release the solver backend's resources.
cleanupContext :: Context -> IO ()
cleanupContext Ctx {..} = do
  maybe (return ()) (hCloseMe "ctxLog") ctxLog
  ctxClose

hCloseMe :: String -> Handle -> IO ()
hCloseMe msg h = hClose h `catch` (\(exn :: IOException) -> putStrLn $ "OOPS, hClose breaks: " ++ msg ++ show exn)

smtPreamble :: Config -> SMTSolver -> Context -> IO [Builder]
smtPreamble cfg s me
  | s == Z3 || s == Z3mem
    = do v <- getZ3Version me
         checkValidStringFlag Z3 v cfg
         return $ makeMbqi ++ makeTimeout cfg ++ Thy.preamble cfg Z3
  | otherwise
    = checkValidStringFlag s [] cfg >> return (makeMbqi ++ Thy.preamble cfg s)
  where
    makeMbqi
      | s == Z3 || s == Z3mem = ["\n(set-option :smt.mbqi " <> (if smtMbqi cfg then "true" else "false") <> ")"]
      | s == Cvc5 && smtMbqi cfg = ["(set-option :mbqi true)"]
      | otherwise = []

checkMbqiFlag :: Config -> IO ()
checkMbqiFlag cfg =
    when (smtMbqi cfg && solver cfg `notElem` [Z3, Z3mem, Cvc5]) $
        die $
            err dummySpan $
                text ("--mbqi is not supported by " ++ show (solver cfg))

getZ3Version :: Context -> IO [Int]
getZ3Version me
  = do -- resp is like (:version "4.8.15")
       resp <- SMTLIB.Backends.command (ctxSolver me) "(get-info :version)"
       case Char8.split '"' resp of
         _:rText:_ -> do
           -- strip off potential " - build hashcode ..." suffix
           let vText = Char8.takeWhile (not . isSpace) rText
           let parsedComponents = [ reads (Char8.unpack cText) | cText <- Char8.split '.' vText ]
           sequence
             [ case pComponent of
                 [(c, "")] -> return c
                 xs -> error $ "Can't parse z3 version: " ++ show xs
             | pComponent <- parsedComponents
             ]
         xs -> error $ "Can't parse z3 (get-info :version): " ++ show xs

checkValidStringFlag :: SMTSolver -> [Int] -> Config -> IO ()
checkValidStringFlag smt v cfg
  = when (noString smt v cfg) $
      die $ err dummySpan (text "stringTheory is only supported by z3 version >=4.2.2")

noString :: SMTSolver -> [Int] -> Config -> Bool
noString smt v cfg
  =  not (noStringTheory cfg)
  && not (smt == Cvc5 || (smt == Z3 && (v >= [4, 4, 2])))
-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop :: SmtM ()
smtPush = interact' Push
smtPop  = interact' Pop

smtComment :: T.Text -> SmtM ()
smtComment t = interact' (Comment t)

smtDecls :: [(Symbol, Sort)] -> SmtM ()
smtDecls = mapM_ $ uncurry smtDecl

smtDecl :: Symbol -> Sort -> SmtM ()
smtDecl x t = do
    me <- get
    let env = ctxSymEnv me
    let ins' = sortSmtSort False env <$> ins
    let out' = sortSmtSort False env out
    interact' (notracepp _msg $ Declare (symbolSmtText x) ins' out')
  where
    (ins, out) = deconSort t
    _msg = "smtDecl: " ++ showpp (x, t, ins, out)

smtFuncDecl :: T.Text -> ([SmtSort],  SmtSort) -> SmtM ()
smtFuncDecl x (ts, t) = interact' (Declare x ts t)

smtDataDecl :: [DataDecl] -> SmtM ()
smtDataDecl ds = interact' (DeclData ds)

deconSort :: Sort -> ([Sort], Sort)
deconSort t = case functionSort t of
                Just (_, ins, out) -> (ins, out)
                Nothing            -> ([], t)

-- Command serialization discovers and declares support before assertion.
smtAssert :: (HasCallStack) => Expr -> SmtM ()
smtAssert p = interact' (Assert Nothing p)

smtDefineEqn :: Equation -> SmtM ()
smtDefineEqn Equ {..} = smtDefineFunc eqName eqArgs eqSort eqBody

smtDefineFunc :: Symbol -> [(Symbol, F.Sort)] -> F.Sort -> Expr -> SmtM ()
smtDefineFunc name parameters result body =
    do
        env <- gets ctxSymEnv
        interact' $
            DefineFunc
                name
                (map (sortSmtSort False env <$>) parameters)
                (sortSmtSort False env result)
                body

-----------------------------------------------------------------

-- | The shared command path declares the axiom's discovered support before
--   asserting it, just as it does for ordinary assertions and definitions.
smtAssertAxiom :: HasCallStack => Triggered Expr -> SmtM ()
smtAssertAxiom p  = interact' (AssertAx p)

smtDistinct :: [Expr] -> SmtM ()
smtDistinct az = interact' (Distinct az)

-- | An error reply fails this action, inside the caller's bracket and span;
--   a lazy 'respSat' would defer it to whoever forces the answer.
smtCheckUnsat :: HasCallStack => SmtM Bool
smtCheckUnsat = do
  response <- command CheckSat
  pure $! respSat response

smtBracketAt :: SrcSpan -> String -> SmtM a -> SmtM a
smtBracketAt sp _msg a =
  smtBracket _msg a `catchSMT` dieAt sp

-- | `smtBracket` adds a new level to the apply stack and saves the last fresh index
--   on the index stack before the action, and reverts these changes after the action.
smtBracket :: String -> SmtM a -> SmtM a
smtBracket msg a = do
  smtComment (T.pack $ "smtBracket - start: " ++ msg)
  smtPush
  r <- a
  smtPop
  smtComment (T.pack $ "smtBracket - end: " ++ msg)
  return r

respSat :: HasCallStack => Response -> Bool
respSat Unsat   = True
respSat Sat     = False
respSat Unknown = False
respSat r       = die $ err dummySpan $ text ("crash: SMTLIB2 respSat = " ++ show r)

interact' :: Command -> SmtM ()
interact' cmd  = void $ command cmd

makeTimeout :: Config -> [Builder]
makeTimeout cfg
  | Just i <- smtTimeout cfg = [ "\n(set-option :timeout " <> fromString (show i) <> ")\n"]
  | otherwise                = [""]


--------------------------------------------------------------------------------
declare :: SmtM ()
--------------------------------------------------------------------------------
declare = do
  me <- get
  let env        = ctxSymEnv me
  let xts        = symbolSorts (F.seSort env)
  let tx         = elaborate (ElabParam (ctxElabF me) "declare" env)
  let lts        = F.toListSEnv . F.seLits $ env
  let dss        = dataDeclarations          env
  let qryXTs     = fmap tx <$> [ (x, t) | (x, t) <- xts, symKind env x `elem` [Nothing, Just F.Uninterp] ]
  -- let isKind n   = (n ==)  . symKind env . fst
  let MkDefinedFuns defs = ctxDefines me
  let ess        = distinctLiterals  lts
  let axs        = Thy.axiomLiterals (config me) lts
  forM_ dss              smtDataDecl
  -- Ordinary functions are values used through apply, not native callables.
  forM_ qryXTs $ \(x, t) ->
    smtFuncDecl (symbolSmtText x) ([], sortSmtSort False env t)
  forM_ defs             smtDefineEqn
  forM_ ess              smtDistinct
  forM_ axs              smtAssert

symbolSorts :: F.SEnv F.Sort -> [(F.Symbol, F.Sort)]
symbolSorts env = [(x, tx t) | (x, t) <- F.toListSEnv env ]
 where
  tx t@(FObj a) = fromMaybe t (F.lookupSEnv a env)
  tx t          = t

dataDeclarations :: SymEnv -> [[DataDecl]]
dataDeclarations = orderDeclarations . map snd . F.toListSEnv . F.seData

-- | See 'F.seDeclarationsCur' for explanation.
funcSortVars :: Bool -> F.SymEnv -> [(T.Text, ([F.SmtSort], F.SmtSort))]
funcSortVars lams env =
    concatMap symbolsForTag $ M.toList $ M.fromList [(sort, index) | (F.ApplyCarrier sort, index) <- M.toList (F.seDeclarationsCur env)]
  where
    symbolsForTag (t, i) =
        let applySym = symbolAtSortIndex applyName i
            coerceSym = symbolAtSortIndex coerceName i
            lamSym = symbolAtSortIndex lambdaName i
            argSyms =
                if lams && snd t == F.SInt
                    then
                        [ (symbolAtSortIndex (lamArgSymbol j) i, argSort t)
                        | j <- [1 .. Thy.maxLamArg]
                        ]
                    else []
         in (applySym, appSort t)
                : (coerceSym, ([fst t], snd t))
                : (lamSym, lamSort t)
                : argSyms

    appSort (s, t) = ([F.SInt, s], t)
    lamSort (s, t) = ([s, t], F.SInt)
    argSort (s, _) = ([], s)

symKind :: F.SymEnv -> F.Symbol -> Maybe Sem
symKind env x = F.tsInterp <$> F.symEnvTheory x env

-- | `distinctLiterals` is used solely to determine the set of literals
--   (of each sort) that are *disequal* to each other, e.g. EQ, LT, GT,
--   or string literals "cat", "dog", "mouse". These should only include
--   non-function sorted values.
distinctLiterals :: [(F.Symbol, F.Sort)] -> [[F.Expr]]
distinctLiterals xts = [ es | (_, es) <- tess ]
   where
    tess             = Misc.groupList [(t, F.expr x) | (x, t) <- xts, notFun t]
    notFun           = not . F.isFunctionSortedReft . (`F.RR` F.trueReft)
    -- _notStr          = not . (F.strSort ==) . F.sr_sort . (`F.RR` F.trueReft)
