module SF2TAL.K (kProg) where

import SF2TAL.F qualified as F
import SF2TAL.Middle
import SF2TAL.Utils


kTy :: F.Ty -> Ty
kTy (F.TVar a) = TVar a
kTy F.TInt = TInt
kTy (t1 `F.TFun` t2) = TFix mempty [kTy t1, kCont t2]
kTy (F.TForall a t) = TFix [a] [kCont t]
kTy (F.TTuple ts) = tTuple $ fmap kTy ts


kCont :: F.Ty -> Ty
kCont t = TFix [] [kTy t]


kProg :: MonadUniq m => F.Tm -> m Tm
kProg v@(F.Ann _u t) = kExp v $ \x -> pure $ Halt (kTy t) x
kProg x = error $ "unannotated: " <> show x


kExp :: MonadUniq m => F.Tm -> (Ann -> m Tm) -> m Tm
kExp (u `F.Ann` t) k = case u of
  F.Var x -> k $ Var x `Ann` kTy t
  F.IntLit v -> k $ IntLit v `Ann` kTy t
  F.Fix x x1 t1 t2 e -> do
    c <- freshName
    e' <- kExp e $ \k' -> pure $ App (Var c `Ann` kCont t2) [] [k']
    k $ Fix x [] [(x1, kTy t1), (c, kCont t2)] e' `Ann` kTy t
  v1 `F.App` v2 -> kExp v1 $ \x1 -> kExp v2 $ \x2 -> do
    k' <- unEta k (kTy t)
    pure $ App x1 [] [x2, k']
  a `F.AbsT` v -> do
    c <- freshName
    v' <- kExp v $ \k' -> pure $ App (Var c `Ann` kCont (F.ann v)) [] [k']
    k $ Fix "" [a] [(c, kCont $ F.ann v)] v' `Ann` kTy t
  v `F.AppT` s -> do
    k' <- unEta k (kTy t)
    kExp v $ \x -> pure $ App x [kTy s] [k']
  F.Tuple vs ->
    foldr
      (\v k' vs' -> kExp v $ \x -> k' (x : vs'))
      (\k' -> k $ Tuple k' `Ann` kTy t)
      vs
      []
  F.At i v -> kExp v $ \x -> do
    y <- freshName
    Let (At y i x) <$> k (Var y `Ann` kTy t)
  F.Arith p e1 e2 -> do
    kExp e1 $ \x1 -> do
      kExp e2 $ \x2 -> do
        y <- freshName
        Let (Arith y p x1 x2) <$> k (Var y `Ann` TInt)
  F.If0 e1 e2 e3 -> do
    kExp e1 $ \x -> do
      e2' <- kExp e2 k
      e3' <- kExp e3 k
      pure $ If0 x e2' e3'
  _ -> error ""
kExp x _ = error $ "unannotated: " <> show x


unEta :: MonadUniq m => (Ann -> m Tm) -> Ty -> m Ann
unEta k t = do
  k' <- freshName
  un <- k $ Var k' `Ann` t
  pure $ Fix "" [] [(k', t)] un `Ann` TFix [] [t]
