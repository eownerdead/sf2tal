module SF2TAL.Middle.FromF
  ( kProg
  )
where

import Control.Monad.State
import Data.Map qualified as M
import Lens.Micro.Platform
import SF2TAL.F qualified as F
import SF2TAL.Middle.Middle
import SF2TAL.Utils


type KT = StateT (M.Map F.Name Name)


freshen :: MonadUniq m => F.Name -> KT m Name
freshen x =
  preuse (ix x) >>= \case
    Just x' -> pure x'
    Nothing -> do
      x' <- fresh
      state \s -> (x', s & at x ?~ x')


kTy :: MonadUniq m => F.Ty -> KT m Ty
kTy = \case
  F.TVar a -> TVar <$> freshen a
  F.TInt -> pure TInt
  t1 `F.TFun` t2 -> TFix mempty <$> sequenceA [kTy t1, kCont t2]
  F.TForall a t -> do
    a' <- freshen a
    t' <- kCont t
    pure $ TFix [a'] [t']
  F.TTuple ts -> tTuple <$> traverse kTy ts


kCont :: MonadUniq m => F.Ty -> KT m Ty
kCont t = do
  t' <- kTy t
  pure $ TFix [] [t']


kProg :: MonadUniq m => F.Tm -> m Tm
kProg v = evalStateT (kExp v (pure . Halt)) mempty


kExp :: MonadUniq m => F.Tm -> (Val -> KT m Tm) -> KT m Tm
kExp (u `F.Ann` t) k = case u of
  F.Var x -> do
    x' <- freshen x
    k . Var x' =<< kTy t
  F.IntLit v -> k $ IntLit v
  F.Fix x x1 t1 t2 e -> do
    x' <- if x == "" then pure Nothing else Just <$> freshen x
    x1' <- freshen x1
    c <- fresh
    t1' <- kTy t1
    t2' <- kCont t2
    e' <- kExp e \k' -> pure $ App (Var c t2') [] [k']
    k $ Fix x' [] [(x1', t1'), (c, t2')] e'
  v1 `F.App` v2 -> kExp v1 \x1 -> kExp v2 \x2 -> do
    k' <- unEta k =<< kTy t
    pure $ App x1 [] [x2, k']
  a `F.AbsT` v -> do
    a' <- freshen a
    c <- fresh
    vt <- kCont (F.ann v)
    v' <- kExp v $ \k' -> pure $ App (Var c vt) [] [k']
    k $ Fix Nothing [a'] [(c, vt)] v'
  v `F.AppT` s -> do
    k' <- unEta k =<< kTy t
    s' <- kTy s
    kExp v \x -> pure $ App x [s'] [k']
  F.Tuple vs ->
    foldr
      (\v k' vs' -> kExp v \x -> k' (x : vs'))
      (k . Tuple)
      vs
      []
  F.At i v -> kExp v \x -> do
    y <- fresh
    Let (At y i x) <$> (k . Var y =<< kTy t)
  F.Arith p e1 e2 -> do
    kExp e1 \x1 -> do
      kExp e2 \x2 -> do
        y <- fresh
        Let (Arith y p x1 x2) <$> k (Var y TInt)
  F.If0 e1 e2 e3 -> do
    kExp e1 \x -> do
      e2' <- kExp e2 k
      e3' <- kExp e3 k
      pure $ If0 x e2' e3'
  _ -> error ""
kExp x _ = error $ "unannotated: " <> show x


unEta :: MonadUniq m => (Val -> m Tm) -> Ty -> m Val
unEta k t = do
  k' <- fresh
  un <- k $ Var k' t
  pure $ Fix Nothing [] [(k', t)] un
