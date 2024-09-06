{-# LANGUAGE ParallelListComp #-}

module SF2TAL.A (aProg) where

import Control.Monad
import Data.Bifunctor
import Data.Foldable
import Lens.Micro.Platform
import SF2TAL.Common
import SF2TAL.Middle


errorH :: Show a => a -> b
errorH x = error $ "not in H: " <> show x


let' :: [Decl] -> Tm -> Tm
let' ds e = foldr Let e ds


aTy :: Ty -> Ty
aTy (TVar a) = TVar a
aTy TInt = TInt
aTy (TFix as ts) = TFix as (fmap aTy ts)
aTy (TTuple ts) = TTuple $ fmap (first aTy) ts
aTy (TExists a t) = TExists a $ aTy t


aProg :: MonadUniq m => Prog -> m Prog
aProg (LetRec xs e) = LetRec <$> traverse aHval xs <*> aExp e


aHval :: MonadUniq m => Ann -> m Ann
aHval (Fix "" as xs e `Ann` t) =
  Ann <$> (Fix "" as (xs <&> _2 %~ aTy) <$> aExp e) <*> pure t
aHval v = error $ "unannotated: " <> show v


aExp :: MonadUniq m => Tm -> m Tm
aExp (Let d e) = let' <$> aDec d <*> aExp e
aExp (App v [] vs) = do
  (ds, v') <- aVal v
  (ds', vs') <- mapAndUnzipM aVal vs
  pure $ let' (ds <> fold ds') $ App v' [] vs'
aExp e@App{} = errorH e
aExp (If0 v e1 e2) = do
  (ds, v') <- aVal v
  let' ds <$> (If0 v' <$> aExp e1 <*> aExp e2)
aExp (Halt t v) = do
  (ds, v') <- aVal v
  pure $ let' ds $ Halt (aTy t) v'


aDec :: MonadUniq m => Decl -> m [Decl]
aDec (Bind x v) = do
  (ds, v') <- aVal v
  pure $ ds <> [Bind x v']
aDec (At x i v) = do
  (ds, v') <- aVal v
  pure $ ds <> [At x i v']
aDec (Bin x p v1 v2) = do
  (ds1, v1') <- aVal v1
  (ds2, v2') <- aVal v2
  pure $ ds1 <> ds2 <> [Bin x p v1' v2']
aDec (Unpack a x v) = do
  (ds, v') <- aVal v
  pure $ ds <> [Unpack a x v']
aDec d@Malloc{} = errorH d
aDec d@Update{} = errorH d


aVal :: MonadUniq m => Ann -> m ([Decl], Ann)
aVal (u `Ann` t) = case u of
  Var x -> pure ([], Var x `Ann` aTy t)
  IntLit i -> pure ([], IntLit i `Ann` aTy t)
  v `AppT` ts -> do
    (ds, v') <- aVal v
    pure (ds, (v' `AppT` aTy ts) `Ann` aTy t)
  Pack t' v t'' -> do
    (ds, v') <- aVal v
    pure (ds, Pack (aTy t') v' (aTy t'') `Ann` aTy t)
  Tuple vs -> do
    let n = length vs
    let ts = fmap (aTy . ty) vs
    (ds, vs') <- unzip <$> traverse aVal vs

    y0 <- freshName
    ys <- replicateM n freshName
    pure
      ( fold ds
          <> [Malloc y0 ts]
          <> [ Update
              y
              (Var y' `Ann` tTupleInitToN (i - 1) (tTupleUninited ts))
              i
              v'
             | y <- ys
             | y' <- y0 : ys
             | v' <- vs'
             | i <- [1 ..]
             ]
      , Var (last (y0 : ys)) `Ann` aTy t
      )
  Fix{} -> errorH u
