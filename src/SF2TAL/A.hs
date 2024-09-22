module SF2TAL.A (aProg) where

import Control.Monad
import Control.Monad.Writer
import Lens.Micro.Platform
import SF2TAL.Common
import SF2TAL.Middle


type AT = WriterT [Decl]


errorH :: Show a => a -> b
errorH x = error $ "not in H: " <> show x


let' :: Monad m => AT m Tm -> m Tm
let' m = uncurry (foldr Let) <$> runWriterT m


aTy :: Ty -> Ty
aTy (TVar a) = TVar a
aTy TInt = TInt
aTy (TFix as ts) = TFix as (fmap aTy ts)
aTy (TTuple ts) = TTuple $ fmap (_1 %~ aTy) ts
aTy (TExists a t) = TExists a $ aTy t


aProg :: MonadUniq m => Prog -> m Prog
aProg (LetRec xs e) = LetRec <$> traverse aHval xs <*> aExp e


aHval :: MonadUniq m => Ann -> m Ann
aHval (Fix "" as xs e `Ann` t) =
  Ann <$> (Fix "" as (xs <&> _2 %~ aTy) <$> aExp e) <*> pure t
aHval v = error $ "unannotated: " <> show v


aExp :: MonadUniq m => Tm -> m Tm
aExp (Let d e) = let' $ aDec d >> aExp e
aExp (App v [] vs) = let' $ App <$> aVal v <*> pure [] <*> traverse aVal vs
aExp e@App{} = errorH e
aExp (If0 v e1 e2) = let' $ If0 <$> aVal v <*> aExp e1 <*> aExp e2
aExp (Halt t v) = let' $ Halt (aTy t) <$> aVal v


aDec :: MonadUniq m => Decl -> AT m ()
aDec (Bind x v) = do
  v' <- aVal v
  tell [Bind x v']
aDec (At x i v) = do
  v' <- aVal v
  tell [At x i v']
aDec (Arith x p v1 v2) = do
  v1' <- aVal v1
  v2' <- aVal v2
  tell [Arith x p v1' v2']
aDec (Unpack a x v) = do
  v' <- aVal v
  tell [Unpack a x v']
aDec d@Malloc{} = errorH d
aDec d@Update{} = errorH d


aVal :: MonadUniq m => Ann -> AT m Ann
aVal (u `Ann` t) = case u of
  Var x -> pure $ Var x `Ann` aTy t
  IntLit i -> pure $ IntLit i `Ann` aTy t
  v `AppT` ts -> do
    v' <- aVal v
    pure $ (v' `AppT` aTy ts) `Ann` aTy t
  Pack t' v t'' -> do
    v' <- aVal v
    pure $ Pack (aTy t') v' (aTy t'') `Ann` aTy t
  Tuple vs -> do
    let n = length vs
    let ts = fmap (aTy . (^. ty)) vs
    vs' <- traverse aVal vs

    y0 <- freshName
    ys <- replicateM n freshName
    writer
      ( Var (last (y0 : ys)) `Ann` aTy t
      , Malloc y0 ts
          : [ Update y (Var y' `Ann` tTupleInitedToN (i - 1) ts) i v'
            | y <- ys
            | y' <- y0 : ys
            | v' <- vs'
            | i <- [1 ..]
            ]
      )
  Fix{} -> errorH u
