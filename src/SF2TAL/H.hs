module SF2TAL.H (hProg) where

import Control.Monad.Writer
import Data.HashMap.Strict qualified as HM
import GHC.Stack (HasCallStack)
import SF2TAL.Common
import SF2TAL.Middle


errorC :: (HasCallStack, Show a) => a -> b
errorC x = error $ "not in C: " <> show x


type HoistT m = WriterT (HM.HashMap Name Ann) m


hProg :: MonadUniq m => Tm -> m Prog
hProg p = do
  (e, xs) <- runWriterT $ hExp p
  pure $ LetRec xs e


hExp :: MonadUniq m => Tm -> HoistT m Tm
hExp (Let d e) = Let <$> hDec d <*> hExp e
hExp (App v ts vs) = App <$> hAnn v <*> pure ts <*> mapM hAnn vs
hExp (If0 v e1 e2) = If0 <$> hAnn v <*> hExp e1 <*> hExp e2
hExp (Halt t v) = Halt t <$> hAnn v


hDec :: MonadUniq m => Decl -> HoistT m Decl
hDec (Bind x v) = Bind x <$> hAnn v
hDec (At x i v) = At x i <$> hAnn v
hDec (Bin x p v1 v2) = Bin x p <$> hAnn v1 <*> hAnn v2
hDec (Unpack a x v) = Unpack a x <$> hAnn v
hDec d@Malloc{} = errorC d
hDec d@Update{} = errorC d


hAnn :: MonadUniq m => Ann -> HoistT m Ann
hAnn (u `Ann` t) = case u of
  Var x -> pure $ Var x `Ann` t
  IntLit i -> pure $ IntLit i `Ann` t
  Fix x as xs e -> do
    x' <- if x == "" then lift freshName else pure x
    e' <- hExp e
    writer (Var x' `Ann` t, HM.singleton x' (Fix "" as xs e' `Ann` t))
  Tuple es -> Ann <$> (Tuple <$> mapM hAnn es) <*> pure t
  v `AppT` t' -> Ann <$> (AppT <$> hAnn v <*> pure t') <*> pure t'
  Pack t1 v t2 -> Ann <$> (Pack t1 <$> hAnn v <*> pure t2) <*> pure t
