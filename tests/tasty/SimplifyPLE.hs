module SimplifyPLE (simplify', simplifyWithConstants) where

import qualified Data.HashMap.Strict as SM
import qualified Data.HashSet as S
import Language.Fixpoint.Solver.PLE (ICtx (..))
import qualified Language.Fixpoint.Solver.PLE as PLE
import Language.Fixpoint.Types.Refinements (Expr)

simplify' :: Expr -> Expr
simplify' = simplifyWithConstants []

simplifyWithConstants :: [(Expr, Expr)] -> Expr -> Expr
simplifyWithConstants constants = PLE.simplify emptyICtx
  where
    emptyICtx :: PLE.ICtx
    emptyICtx =
        ICtx
            { icAssms = S.empty -- S.HashSet Pred
            , icCands = mempty -- :: S.HashSet Expr
            , icEquals = mempty -- :: EvAccum
            , icSimpl = SM.fromList constants -- :: !ConstMap
            , icSubcId = Nothing -- :: Maybe SubcId
            , icANFs = [] -- :: [[(Symbol, SortedReft)]]
            , icLRWs = mempty
            , icEtaBetaFlag = False
            , icExtensionalityFlag = False
            , icLocalRewritesFlag = False
            , icBindIds = mempty
            , icFreshExistentialCounter = 0
            , icInitialLHSs = mempty
            }
