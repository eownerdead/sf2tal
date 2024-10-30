module SF2TAL.Tal.FromA (tProg) where

import Control.Monad
import Control.Monad.RWS
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import GHC.Generics
import Lens.Micro.Platform
import SF2TAL.Middle qualified as M
import SF2TAL.Tal.Tal
import SF2TAL.Utils


tTy :: M.Ty -> Ty
tTy = \case
  M.TVar a -> TVar a
  M.TInt -> TInt
  M.TFix as ts ->
    TCode as $
      M.fromList $
        zip (fmap A [(1 :: Int) ..]) (fmap tTy ts)
  M.TTuple ts -> TTuple $ ts <&> _1 %~ tTy
  M.TExists a t -> TExists a (tTy t)


type Vals = M.Map Name Val


data TalEnv = TalEnv
  { vals :: Vals
  , tCtx :: S.Set TName
  , tRegFile :: TRegFile
  }


makeFieldsId ''TalEnv


data TalLog = TalLog
  { heaps :: Heaps
  , tHeap :: THeap
  }


deriving stock instance Show TalLog


deriving stock instance Generic TalLog


deriving via (Generically TalLog) instance Semigroup TalLog


deriving via (Generically TalLog) instance Monoid TalLog


makeFieldsId ''TalLog


type TalT m a = RWST TalEnv TalLog () m a


tProg :: MonadUniq m => M.Prog -> m (Prog, THeap)
tProg p = do
  (is, hs) <-
    evalRWST
      (tProg' p)
      TalEnv{vals = mempty, tCtx = mempty, tRegFile = mempty}
      ()
  pure (Prog (hs ^. heaps) mempty is, hs ^. tHeap)


tProg' :: MonadUniq m => M.Prog -> TalT m Seq
tProg' (M.LetRec xs e) = do
  vs <- traverse (const fresh) xs
  local (vals .~ fmap Label vs) do
    hs' <- traverse (tHVal . (^. M.val)) $ M.mapKeys (vs M.!) xs
    is <- tExp e
    writer (is, TalLog hs' $ tTy . (^. M.ty) <$> M.mapKeys (vs M.!) xs)


tHVal :: MonadUniq m => M.Val -> TalT m HVal
tHVal = \case
  M.Fix Nothing as xs e -> do
    let trs = M.fromList [(A i, tTy $ x ^. _2) | i <- [1 ..] | x <- xs]
    let vs' = M.fromList [(x ^. _1, Reg $ A i) | i <- [1 ..] | x <- xs]
    is <-
      local
        do (vals <>~ vs') . (tCtx .~ S.fromList as) . (tRegFile .~ trs)
        do tExp e
    pure $ Code as trs is
  M.Tuple vs -> Tuple <$> traverse tVal vs
  h -> error $ "not HVal: " <> T.unpack (prettyText h)


tVal :: MonadUniq m => M.Ann -> TalT m Val
tVal (u `M.Ann` _) = case u of
  M.Var x ->
    preview (vals . ix x) >>= \case
      Just x' -> pure x'
      Nothing -> error $ "undefined variable " <> T.unpack (prettyText x)
  M.IntLit i -> pure $ IntLit i
  M.AppT v s -> AppT <$> tVal v <*> pure (tTy s)
  M.Pack t1 v t2 -> Pack (tTy t1) <$> tVal v <*> pure (tTy t2)
  _ -> error $ "not Val: " <> T.unpack (prettyText u)


tExp :: MonadUniq m => M.Tm -> TalT m Seq
tExp = \case
  M.Let d e -> case d of
    M.Bind x v -> do
      r <- R <$> fresh
      v' <- tVal v
      is <-
        local
          do (vals . at x ?~ Reg r) . (tRegFile . at r ?~ tTy (v ^. M.ty))
          do tExp e
      pure $ Mov r v' `Seq` is
    M.At x i v
      | M.TTuple ts <- v ^. M.ty -> do
          r <- R <$> fresh
          v' <- tVal v
          is <-
            local
              do
                (vals . at x ?~ Reg r)
                  . (tRegFile . at r ?~ tTy (ts ^?! ix (i - 1) . _1))
              do tExp e
          pure $ Mov r v' `Seq` Ld r r (i - 1) `Seq` is
      | otherwise ->
          error $
            "At: t is not TTuple, but " <> T.unpack (prettyText $ v ^. M.ty)
    M.Arith x p v1 v2 -> do
      r <- R <$> fresh
      v1' <- tVal v1
      v2' <- tVal v2
      is <-
        local
          do (vals . at x ?~ Reg r) . (tRegFile . at r ?~ TInt)
          do tExp e
      pure $ Mov r v1' `Seq` Arith p r r v2' `Seq` is
    M.Unpack a x v@(_ `M.Ann` t)
      | M.TExists _b _t' <- t -> do
          r <- R <$> fresh
          v' <- tVal v
          is <-
            local
              do
                (vals . at x ?~ Reg r)
                  . (tCtx %~ S.insert a)
                  . (tRegFile . at r ?~ tTy t)
              do tExp e
          pure $ Unpack a r v' `Seq` is
      | otherwise -> error $ "t is not TExists, but " <> T.unpack (prettyText t)
    M.Malloc x ts -> do
      r <- R <$> fresh
      is <-
        local
          do
            (vals . at x ?~ Reg r)
              . (tRegFile . at r ?~ TTuple (fmap (\t -> (tTy t, False)) ts))
          do tExp e
      pure $ Malloc r (fmap tTy ts) `Seq` is
    M.Update x v1 i v2
      | M.TTuple ts <- v1 ^. M.ty -> do
          r <- R <$> fresh
          v1' <- tVal v1
          r' <- R <$> fresh
          v2' <- tVal v2
          is <-
            local
              do
                (vals . at x ?~ Reg r)
                  . ( tRegFile
                        . at r
                        ?~ TTuple ((ts <&> _1 %~ tTy) & ix (i - 1) . _2 .~ True)
                    )
              do tExp e
          pure $ Mov r v1' `Seq` Mov r' v2' `Seq` St r (i - 1) r' `Seq` is
      | otherwise ->
          error $
            "Update: t is not TTuple, but " <> T.unpack (prettyText $ v1 ^. M.ty)
  M.App v as vs -> do
    unless (null as) $ error "not (null as)"
    r0 <- R <$> fresh
    rs <- replicateM (length vs) (R <$> fresh)
    v' <- tVal v
    vs' <- traverse tVal vs
    pure $
      foldr Seq (Jmp $ Reg r0) $
        Mov r0 v'
          : [Mov r' v'' | r' <- rs | v'' <- vs']
            <> [Mov (A r) (Reg r') | r <- [(1 :: Int) ..] | r' <- rs]
  M.If0 v e1 e2 -> do
    r <- R <$> fresh
    l <- fresh
    is1 <- tExp e1
    is2 <- tExp e2
    v' <- tVal v
    tCtx' <- view tCtx
    trs <- view tRegFile
    tell $
      TalLog
        do M.singleton l $ Code (S.toList tCtx') trs is2
        do M.singleton l $ TCode (S.toList tCtx') trs
    pure $ Mov r v' `Seq` Bnz r (Label l) `Seq` is1
  M.Halt t v -> do
    v' <- tVal v
    pure $ Mov (A 1) v' `Seq` Halt (tTy t)
