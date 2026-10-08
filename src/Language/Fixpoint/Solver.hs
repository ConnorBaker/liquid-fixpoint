-- | This module implements the top-level API for interfacing with Fixpoint
--   In particular it exports the functions that solve constraints supplied
--   either as .fq files or as FInfo.
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DoAndIfThenElse     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Solver (
    -- * Invoke Solver on an FInfo
    solve

    -- * Invoke Solver on a .fq file
  , solveFQ

    -- * Function to determine outcome
  , resultExit
  , resultExitCode

    -- * Parse Qualifiers from File
  , parseFInfo

    -- * Simplified Info
  , simplifyFInfo
) where

import           Control.Concurrent                 (setNumCapabilities)
import qualified Data.HashMap.Strict              as HashMap
import qualified Data.List                       as L
import qualified Data.Store                       as S
import           Data.Aeson                         (ToJSON, encode)
import qualified Data.Text.Lazy.IO                as LT
import qualified Data.Text.Lazy.Encoding          as LT
import           System.Exit                        (ExitCode (..))
import           Language.Fixpoint.Verbosity   (whenNormal, whenLoud)
import           Control.Monad                      (when, foldM)
import           Control.Exception                  (SomeException, catch)
import           Control.Exception.Compat
    (ExceptionWithContext(..), displayExceptionContext, wrapExceptionWithContext)
import           Language.Fixpoint.Solver.EnvironmentReduction
  (reduceEnvironments, simplifyBindings)
import           Language.Fixpoint.Solver.Sanitize  (symbolEnv, sanitize, shareFunctionLets)
import           Language.Fixpoint.Solver.UniqifyBinds (renameAll)
import           Language.Fixpoint.Defunctionalize (defunctionalize)
import           Language.Fixpoint.SortCheck            (ElabParam (..), Elaborate (..), theoryEnv)
import           Language.Fixpoint.Solver.Extensionality (expand)
import           Language.Fixpoint.Solver.Prettify (savePrettifiedQuery)
import           Language.Fixpoint.Solver.UniqifyKVars (wfcUniqify, FormalOrigin (..), WfOrigins)
import qualified Language.Fixpoint.Solver.Solve     as Sol
import qualified Language.Fixpoint.Solver.Solution  as Sol
import           Language.Fixpoint.Types.Config
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files            hiding (Result)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Utils.Statistics (statistics)
import           Language.Fixpoint.Graph
import           Language.Fixpoint.Parse            (rr')
import           Language.Fixpoint.Types hiding (GInfo(..), fi)
import qualified Language.Fixpoint.Types as Types (GInfo(..))
import           Language.Fixpoint.Minimize (minQuery, minQuals, minKvars)
import           Control.DeepSeq
import           Data.Functor                        (void)
import qualified Data.ByteString as B
import qualified Data.HashSet as HS
import Data.Maybe (catMaybes)
import qualified Text.PrettyPrint.HughesPJ as PJ

---------------------------------------------------------------------------
-- | Solve an .fq file ----------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
solveFQ cfg = do
    (fi, opts) <- readFInfo file
    cfg'       <- withPragmas cfg opts
    let fi'     = ignoreQualifiers cfg' fi
    r          <- solve cfg' fi'
    resultExitCode cfg (fst <$> r)
  where
    file    = srcFile      cfg

---------------------------------------------------------------------------
resultExitCode :: (Fixpoint a, NFData a, ToJSON a) => Config -> Result a
               -> IO ExitCode
---------------------------------------------------------------------------
resultExitCode cfg r = do
  whenNormal $ colorStrLn (colorResult stat) (statStr $!! stat)
  when (json cfg) $ LT.putStrLn jStr
  return (eCode r)
  where
    jStr    = LT.decodeUtf8 . encode $ r
    stat    = resStatus $!! r
    eCode   = resultExit . resStatus
    statStr = PJ.render . resultDoc

ignoreQualifiers :: Config -> FInfo a -> FInfo a
ignoreQualifiers cfg fi
  | eliminate cfg == All = fi { Types.quals = [] }
  | otherwise            = fi


--------------------------------------------------------------------------------
-- | Solve FInfo system of horn-clause constraints -----------------------------
--------------------------------------------------------------------------------
solve
  :: (PPrint a, NFData a, Fixpoint a, Show a, Loc a)
  => Config -> FInfo a -> IO (Result (Integer, a))
--------------------------------------------------------------------------------
solve cfg q
  | parts cfg      = partition  cfg        $!! q
  | stats cfg      = statistics cfg        $!! q
  | minimize cfg   = minQuery   cfg solve' $!! q
  | minimizeQs cfg = minQuals cfg solve'   $!! q
  | minimizeKs cfg = minKvars cfg solve'   $!! q
  | otherwise      = solve'     cfg        $!! q


solve'
  :: (PPrint a, NFData a, Fixpoint a, Show a, Loc a)
  => Config -> FInfo a -> IO (Result (Integer, a))
solve' cfg q = do
    when (save cfg) $ saveQuery cfg q
    res <- if multicore cfg then
             solvePar cfg q
           else
             solveNative cfg (slice cfg q)
    when (saveBfqOnError cfg && isUnsafe res) $ saveBinaryQuery cfg (void q)
    return res

--------------------------------------------------------------------------------
readFInfo :: FilePath -> IO (FInfo (), [String])
--------------------------------------------------------------------------------
readFInfo f
  | isBinary f = (,) <$> readBinFq f <*> return []
  | otherwise  = readFq f

readFq :: FilePath -> IO (FInfo (), [String])
readFq file = do
  str   <- readFile file
  let q  = {- SCC "parsefq" -} rr' file str :: FInfoWithOpts ()
  return (fioFI q, fioOpts q)

readBinFq :: FilePath -> IO (FInfo ())
readBinFq file = {-# SCC "parseBFq" #-} do
  bs <- B.readFile file
  case S.decode bs of
    Right fi -> return fi
    Left err' -> error ("Error decoding .bfq: " ++ show err')

--------------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
--------------------------------------------------------------------------------
solvePar
  :: (Loc a, NFData a, PPrint a, Show a, Fixpoint a)
  => Config -> FInfo a -> IO (Result (Integer, a))
--------------------------------------------------------------------------------
solvePar c fi0 = do
  -- putStrLn "Using Parallel Solver \n"
  let fi    = slice c fi0
  mci      <- mcInfo c
  let fis   = partition' (Just mci) fi
  writeLoud $ "Number of partitions : " ++ show (length fis)
  writeLoud $ "number of cores      : " ++ show (cores c)
  writeLoud $ "minimum part size    : " ++ show (minPartSize c)
  writeLoud $ "maximum part size    : " ++ show (maxPartSize c)
  case fis of
    []        -> errorstar "partiton' returned empty list!"
    [onePart] -> solveNative c onePart
    _         -> inParallelUsing (f c) $ zip [1..] fis
    where
      f c' (j, fi) = solveNative (c {srcFile = queryFile (Part j) c'}) fi

--------------------------------------------------------------------------------
-- | Solve a list of FInfos using the provided solver function in parallel
--------------------------------------------------------------------------------
inParallelUsing :: (a -> IO (Result b)) -> [a] -> IO (Result b)
--------------------------------------------------------------------------------
inParallelUsing f xs = do
   setNumCapabilities (length xs)
   rs <- asyncMapM f xs
   return $ either conflict id (foldM mergeResult safe rs)
  where
    conflict message = Result (Crash [] message) mempty mempty mempty
    mergeResult prior next
      | not (valid prior && valid next) = Left "partition result has inconsistent KVar scope coverage"
      | not (HS.null (HS.intersection (keys prior) (keys next))) = Left "parallel partitions export the same KVar"
      | otherwise = Right $ Result
          (resStatus prior <> resStatus next)
          (HashMap.union (resSolution prior) (resSolution next))
          (HashMap.union (resNonCutsSolution prior) (resNonCutsSolution next))
          (HashMap.union (resScopes prior) (resScopes next))
    valid result =
      HS.null (HS.intersection (HashMap.keysSet (resSolution result)) (HashMap.keysSet (resNonCutsSolution result)))
        && HashMap.keysSet (resScopes result) == keys result
    keys result = HS.union (HashMap.keysSet (resSolution result)) (HashMap.keysSet (resNonCutsSolution result))


--------------------------------------------------------------------------------
-- | Native Haskell Solver -----------------------------------------------------
--------------------------------------------------------------------------------
solveNative, solveNative'
  :: (NFData a, Fixpoint a, Show a, Loc a, PPrint a)
  => Config -> FInfo a -> IO (Result (Integer, a))
--------------------------------------------------------------------------------
solveNative !cfg !fi0 = solveNative' cfg fi0
                          `catch`
                             (return . crashResult (errorMap fi0) . wrapExceptionWithContext)
                          `catch`
                             (return . crashResultOther . wrapExceptionWithContext)

crashResult :: (PPrint a) => ErrorMap a -> ExceptionWithContext Error -> Result (Integer, a)
crashResult m (ExceptionWithContext ectx ex) = Result res mempty mempty mempty
  where
    res = Crash es msg
    es  = catMaybes [ findError m e | e <- ers ]
    ers = errs ex
    msg = displayExceptionContext ectx ++ "\n" ++ msg0
    msg0 | null ers = "Sorry, unexpected panic in liquid-fixpoint!\n"
                       ++ showpp ex
         | otherwise = showpp ex

crashResultOther
  :: ExceptionWithContext SomeException -> Result (Integer, a)
crashResultOther (ExceptionWithContext ectx ex) =
    Result res mempty mempty mempty
  where
    res = Crash [] msg
    msg = displayExceptionContext ectx ++ "\n" ++ msg0
    msg0 = "Sorry, unexpected panic in liquid-fixpoint!\n" ++ show ex

-- | Unpleasant hack to save meta-data that can be recovered from SrcSpan
type ErrorMap a = HashMap.HashMap SrcSpan a

findError :: ErrorMap a -> Error1 -> Maybe ((Integer, a), Maybe String)
findError m e = do
  ann <- HashMap.lookup (errLoc e) m
  let str = PJ.render (errMsg e)
  return ((-1, ann), Just str)

-- The order is important here: we want the "binders" to get the "precedence"
errorMap :: (Loc a) => FInfo a -> ErrorMap a
errorMap fi = HashMap.fromList [ (srcSpan a, a) | a <- anns ]
  where
    anns    =  [ sinfo c | (_, c) <- HashMap.toList (Types.cm fi) ]
            ++ [ winfo w | (_, w) <- HashMap.toList (Types.ws fi) ]
            ++ [ a | (_, (_,_, a)) <- bindEnvToList (Types.bs fi) ]

loudDump :: (Fixpoint a) => Int -> Config -> SInfo a -> IO ()
loudDump i cfg si = when False (writeLoud $ msg ++ PJ.render (toFixpoint cfg si))
  where
    msg           = "fq file after Uniqify & Rename " ++ show i ++ "\n"

{-# SCC simplifyFInfo #-}
simplifyFInfo :: (NFData a, Fixpoint a, Show a, Loc a)
               => Config -> FInfo a -> IO (ElabParam, SInfo a, SInfo a, SourceScopes)
simplifyFInfo !cfg !fi0 = do
  -- writeLoud $ "fq file in: \n" ++ render (toFixpoint cfg fi)
  -- rnf fi0 `seq` donePhase Loud "Read Constraints"
  -- let qs   = quals fi0
  -- whenLoud $ print qs
  -- whenLoud $ putStrLn $ showFix (quals fi1)
  reducedFi <- reduceFInfo cfg fi0
  let fi1   = reducedFi { Types.quals = remakeQual <$> Types.quals reducedFi }
  let si0   = {- SCC "convertFormat" -} convertFormat fi1
  -- writeLoud $ "fq file after format convert: \n" ++ render (toFixpoint cfg si0)
  -- rnf si0 `seq` donePhase Loud "Format Conversion"
  let si1   = either die id ({- SCC "sanitize" -} sanitize cfg $!! si0)
  -- writeLoud $ "fq file after sanitize: \n" ++ render (toFixpoint cfg si1)
  -- rnf si1 `seq` donePhase Loud "Validated Constraints"
  graphStatistics cfg si1
  let (origins, si2) = {- SCC "wfcUniqify" -} wfcUniqify $!! si1
  -- writeLoud $ "fq file after wfcUniqify: \n" ++ render (toFixpoint cfg si2)
  let si3  = {- SCC "renameAll"  -} renameAll  $!! si2
      sourceScopes = either (die . err dummySpan . PJ.text) id (validateOrigins origins si3)
  rnf si3 `seq` whenLoud $ donePhase Loud "Uniqify & Rename"
  loudDump 1 cfg si3
  let si4  = {- SCC "defunction" -} defunctionalize cfg $!! shareFunctionLets cfg si3
  -- writeLoud $ "fq file after defunc: \n" ++ render (toFixpoint cfg si4)
  -- putStrLn $ "AXIOMS: " ++ showpp (asserts si4)
  loudDump 2 cfg si4
  let ef = solverFlags cfg
      elabParam = ElabParam
                     ef
                     (atLoc dummySpan "solver")
                     (symbolEnv cfg si4)
      si5  = elaborate elabParam si4
  -- writeLoud $ "fq file after elaborate: \n" ++ render (toFixpoint cfg si5)
  loudDump 3 cfg si5
  let si6 = if extensionality cfg then {- SCC "expand" -} expand cfg si5 else si5
  return (elabParam, si5, si6, sourceScopes){- SCC "elaborate" -}

validateOrigins :: WfOrigins -> SInfo a -> Either String SourceScopes
validateOrigins origins fi
  | HashMap.keysSet origins /= HashMap.keysSet (Types.ws fi) = Left "KVar origin and WF keysets differ"
  | otherwise = HashMap.traverseWithKey validateOne origins
  where
    binders = HashMap.fromList (bindEnvToList (Types.bs fi))
    validateOne k entries = do
      w <- maybe (Left "KVar origin has no WF") Right (HashMap.lookup k (Types.ws fi))
      let binderIds = [i | BindOrigin _ i <- entries]
          valueIds = [i | ValueOrigin _ i <- entries]
          wfIds = elemsIBindEnv (wenv w)
      valueBindings <- traverse lookupOrigin valueIds
      if wkvar w == k && L.sort [(name, sr_sort sr) | (name, sr, _) <- valueBindings] == L.sort (wvvs w)
        && length valueIds == HS.size (HS.fromList valueIds)
        && length binderIds == length wfIds && HS.fromList binderIds == HS.fromList wfIds
        then Right ()
        else Left "KVar origins do not cover every WF occurrence exactly once"
      mapped <- foldM (insertOrigin w) HashMap.empty entries
      finalBinders <- traverse lookupOrigin wfIds
      if HashMap.keysSet mapped == HS.fromList (map fst (wvvs w) ++ [name | (name, _, _) <- finalBinders])
        then Right mapped
        else Left "KVar origin does not cover the final WF domain"
    insertOrigin w mapped origin = do
      (canonical, source) <- case origin of
        ValueOrigin source i -> do
          (bound, sr, _) <- lookupOrigin i
          if (bound, sr_sort sr) `elem` wvvs w then Right (bound, source) else Left "KVar value binder changed without its WF value"
        BindOrigin source i -> do
          if memberIBindEnv i (wenv w) then Right () else Left "KVar binder origin left its WF scope"
          (canonical, _, _) <- lookupOrigin i
          Right (canonical, source)
      case HashMap.lookup canonical mapped of
        Nothing -> Right (HashMap.insert canonical source mapped)
        Just previous
          | previous == source -> Right mapped
          | otherwise -> Left "distinct KVar sources collapsed to one canonical formal"
    lookupOrigin i = maybe (Left "KVar origin binder is missing") Right (HashMap.lookup i binders)

reduceFInfo :: Fixpoint a => Config -> FInfo a -> IO (FInfo a)
reduceFInfo cfg fi = do
  let simplifiedFi = {- SCC "simplifyFInfo" -} simplifyBindings cfg fi
      reducedFi = {- SCC "reduceEnvironments" -} reduceEnvironments simplifiedFi
  when (save cfg) $
    savePrettifiedQuery cfg reducedFi
  if noEnvReduction cfg then
    return fi
  else
    return reducedFi

solveNative' !cfg !fi0 = do
  (elabParam, source, si6, sourceScopes) <- simplifyFInfo cfg fi0
  let scope = sInfoScope cfg si6
  res {- SCC "Sol.solve" -} <- Sol.solve cfg source elabParam scope sourceScopes $!! si6
  -- rnf soln `seq` donePhase Loud "Solve2"
  -- let stat = resStatus res
  -- saveSolution cfg res
  when (save cfg) $ Sol.saveSolution cfg "" res
  -- writeLoud $ "\nSolution:\n"  ++ showpp (resSolution res)
  -- colorStrLn (colorResult stat) (show stat)
  return res

--------------------------------------------------------------------------------
-- | Scope ---------------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Computes the set of all symbols that may appear free in expressions
-- within the constraint system.
sInfoScope :: Config -> SInfo a -> HS.HashSet Symbol
sInfoScope cfg si = let base = HS.unions
                          [ HS.fromList [ sym | (_, (sym, _, _)) <- bindEnvToList (Types.bs si) ]
                          , HS.fromList $ map fst $ toListSEnv (Types.gLits si)
                          , HS.fromList $ map fst $ toListSEnv (Types.dLits si)
                          , HS.fromList [ val (dcName dc) | dd <- Types.ddecls si, dc <- ddCtors dd ]
                          , HS.fromList [ val (dfName df) | dd <- Types.ddecls si, dc <- ddCtors dd, df <- dcFields dc ]
                          -- Reflected equation names
                          , HS.fromList [ eqName eq | eq <- aenvEqs (Types.ae si) ]
                          -- WF constraints: the value variables of kvars
                          , HS.fromList [ v | w <- HashMap.elems (Types.ws si), (v, _) <- wvvs w ]
                          -- Theory symbols (arr_store_m, set operations, etc.)
                          , HS.fromList $ map fst $ toListSEnv (theoryEnv cfg si)
                          -- Wired-in symbols used by elaboration
                          , HS.fromList [toIntName, tyCastName, applyName]
                          ]
                    in base `HS.union` HS.map tidySymbol base

--------------------------------------------------------------------------------
-- | Parse External Qualifiers -------------------------------------------------
--------------------------------------------------------------------------------
parseFInfo :: [FilePath] -> IO (FInfo a)
--------------------------------------------------------------------------------
parseFInfo fs = mconcat <$> mapM parseFI fs

parseFI :: FilePath -> IO (FInfo a)
parseFI f = do
  str   <- readFile f
  let fi = rr' f str :: FInfo ()
  return $ mempty { Types.quals = Types.quals  fi
                  , Types.gLits = Types.gLits  fi
                  , Types.dLits = Types.dLits  fi }
