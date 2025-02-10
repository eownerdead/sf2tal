module SF2TAL.Middle.FromC
  ( aProg
  )
where

import Control.Monad
import Control.Monad.Writer
import Lens.Micro.Platform
import SF2TAL.Middle.Middle
import SF2TAL.Utils


type AT = WriterT [Decl]


errorC :: Show a => a -> b
errorC x = error $ "not in C: " <> show x


let' :: Monad m => AT m Tm -> m Tm
let' m = uncurry (foldr Let) <$> runWriterT m


aTy :: Ty -> Ty
aTy = \case
  TVar a -> TVar a
  TInt -> TInt
  TFix as ts -> TFix as (fmap aTy ts)
  TTuple ts -> TTuple $ fmap (_1 %~ aTy) ts
  TExists a t -> TExists a $ aTy t


aProg :: MonadUniq m => Prog -> m Prog
aProg (LetRec xs e) = LetRec <$> traverse aHval xs <*> aExp e


aHval :: MonadUniq m => Val -> m Val
aHval = \case
  Fix Nothing as xs e ->
    Fix Nothing as (xs <&> _2 %~ aTy) <$> aExp e
  v -> error $ "unannotated: " <> show v


aExp :: MonadUniq m => Tm -> m Tm
aExp = \case
  Let d e -> let' $ aDec d >> aExp e
  App v [] vs -> let' $ App <$> aVal v <*> pure [] <*> traverse aVal vs
  e@App{} -> errorC e
  If0 v e1 e2 -> let' $ If0 <$> aVal v <*> aExp e1 <*> aExp e2
  Halt v -> let' $ Halt <$> aVal v


aDec :: MonadUniq m => Decl -> AT m ()
aDec = \case
  Bind x v -> do
    v' <- aVal v
    tell [Bind x v']
  At x i v -> do
    v' <- aVal v
    tell [At x i v']
  Arith x p v1 v2 -> do
    v1' <- aVal v1
    v2' <- aVal v2
    tell [Arith x p v1' v2']
  Unpack a x v -> do
    v' <- aVal v
    tell [Unpack a x v']
  d@Malloc{} -> errorC d
  d@Update{} -> errorC d


aVal :: MonadUniq m => Val -> AT m Val
aVal = \case
  Var x t -> pure $ Var x (aTy t)
  IntLit i -> pure $ IntLit i
  v `AppT` ts -> do
    v' <- aVal v
    pure $ v' `AppT` aTy ts
  Pack t' v t'' -> do
    v' <- aVal v
    pure $ Pack (aTy t') v' (aTy t'')
  v@(Tuple vs) -> do
    let n = length vs
    let ts = fmap (aTy . ty) vs
    vs' <- traverse aVal vs

    y0 <- fresh
    ys <- replicateM n fresh
    writer
      ( Var (last (y0 : ys)) (aTy $ ty v)
      , Malloc y0 ts
          : [ Update y (Var y' $ tTupleInitedToN (i - 1) ts) i v'
            | y <- ys
            | y' <- y0 : ys
            | v' <- vs'
            | i <- [1 ..]
            ]
      )
  v@Fix{} -> errorC v
