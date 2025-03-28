module SF2TAL.Middle.FromF
  ( kProg
  )
where

import Data.Map qualified as M
import Effectful
import Effectful.State.Static.Local.Microlens
import Lens.Micro.Platform hiding (preuse)
import SF2TAL.F qualified as F
import SF2TAL.Middle.Middle
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Uniq


type K es = (Uniq :> es, State (M.Map F.TName Int) :> es)


freshen :: K es => F.TName -> Eff es Int
freshen x =
  preuse (ix x) >>= \case
    Just x' -> pure x'
    Nothing -> do
      x' <- fresh
      state \s -> (x', s & at x ?~ x')


kTy :: K es => F.Ty -> Eff es Ty
kTy = \case
  F.TVar a -> TVar <$> freshen a
  F.TInt -> pure TInt
  t1 `F.TFun` t2 -> TFix mempty <$> sequenceA [kTy t1, kCont t2]
  F.TForall a t -> do
    a' <- freshen a
    t' <- kCont t
    pure $ TFix [a'] [t']
  F.TTuple ts -> tTuple <$> traverse kTy ts


kCont :: K es => F.Ty -> Eff es Ty
kCont t = do
  t' <- kTy t
  pure $ TFix [] [t']


kProg :: Uniq :> es => F.Tm -> Eff es Tm
kProg v = evalState mempty do
  kExp v (pure . Halt)


-- η-expansion
expand :: K es => (Val -> Eff es Tm) -> Ty -> (Val -> Eff es Tm) -> Eff es Tm
expand k t k' = do
  c <- freshName
  kk <- k $ Var c t
  x <- freshName
  LetRec (M.fromList [(x, Abs [] [(c, t)] kk)]) <$> k' (Var x $ TFix [] [t])


kAbs :: K es => F.Tm -> Eff es Val
kAbs = \case
  F.Abs x1 (Just t) e -> do
    t1' <- kTy t
    t2' <- kCont (F.tyOf e)
    c <- freshName
    Abs [] [(x1, t1'), (c, t2')] <$> kExp e \k' ->
      pure $ App (Var c t2') [] [k']
  F.AbsT a e -> do
    a' <- freshen a
    t' <- kCont $ F.tyOf e
    c <- freshName
    Abs [a'] [(c, t')] <$> kExp e \k' -> pure $ App (Var c t') [] [k']
  e -> error $ docStr $ "kAbs:" <+> pp e


kExp :: K es => F.Tm -> (Val -> Eff es Tm) -> Eff es Tm
kExp e k = case e of
  F.Var x (Just t) -> do
    k . Var x =<< kTy t
  F.Var x Nothing -> error $ "Unannotated variable: " <> docStr (pp x)
  F.IntLit i -> k $ IntLit i
  F.LetRec xs e' -> do
    xs' <- traverse kAbs xs
    LetRec xs' <$> kExp e' k
  F.Abs{} -> do
    x <- freshName
    t' <- kTy $ F.tyOf e
    e' <- kAbs e
    LetRec (M.fromList [(x, e')]) <$> k (Var x t')
  e1 `F.App` e2 -> kExp e1 \x1 -> kExp e2 \x2 -> do
    t' <- kTy $ F.tyOf e
    expand k t' \k' ->
      pure $ App x1 [] [x2, k']
  F.AbsT{} -> do
    x <- freshName
    t' <- kTy $ F.tyOf e
    e' <- kAbs e
    LetRec (M.fromList [(x, e')]) <$> k (Var x t')
  e' `F.AppT` s -> do
    t' <- kTy $ F.tyOf e
    s' <- kTy s
    expand k t' \k' ->
      kExp e' \x -> pure $ App x [s'] [k']
  F.Tuple vs ->
    foldr
      (\v k' vs' -> kExp v \x -> k' (x : vs'))
      (k . Tuple)
      vs
      []
  F.At i e'
    | F.TTuple ts <- F.tyOf e'
    , Just t <- ts ^? ix (i - 1) -> kExp e' \x -> do
        y <- freshName
        Let (At y i x) <$> (k . Var y =<< kTy t)
    | otherwise -> error $ docStr $ "At: " <> pp e
  F.Arith p e1 e2 -> do
    kExp e1 \x1 -> do
      kExp e2 \x2 -> do
        y <- freshName
        Let (Arith y p x1 x2) <$> k (Var y TInt)
  F.If0 e1 e2 e3 -> do
    kExp e1 \x -> do
      e2' <- kExp e2 k
      e3' <- kExp e3 k
      pure $ If0 x e2' e3'
  _ -> error $ docStr $ "kExp: " <> pp e
