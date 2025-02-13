module SF2TAL.Tal.FromA (tProg) where

import Control.Monad
import Control.Monad.RWS
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Text qualified as T
import GHC.Generics
import Lens.Micro.Platform
import SF2TAL.Middle qualified as M
import SF2TAL.Tal.Tal
import SF2TAL.Utils


tTy :: M.Ty -> Ty
tTy (M.TVar a) = TVar a
tTy M.TInt = TInt
tTy (M.TFix as ts) =
  TCode as $
    HM.fromList $
      zip (fmap (T.pack . show) [(1 :: Int) ..]) (fmap tTy ts)
tTy (M.TTuple ts) = TTuple $ ts <&> _1 %~ tTy
tTy (M.TExists a t) = TExists a (tTy t)


type Vals = HM.HashMap Name Val


data TalEnv = TalEnv
  { vals :: Vals
  , tCtx :: HS.HashSet TName
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
      (TalEnv{vals = mempty, tCtx = mempty, tRegFile = mempty})
      ()
  pure (Prog (hs ^. heaps) mempty is, hs ^. tHeap)


tProg' :: MonadUniq m => M.Prog -> TalT m Seq
tProg' (M.LetRec xs e) = do
  vs <- traverse (const freshName) xs
  local (vals .~ fmap Label vs) $ do
    hs' <- traverse (tHVal . (^. M.val)) $ HM.mapKeys (vs HM.!) xs
    is <- tExp e
    writer (is, TalLog hs' $ tTy . (^. M.ty) <$> HM.mapKeys (vs HM.!) xs)


tHVal :: MonadUniq m => M.Val -> TalT m HVal
tHVal (M.Fix "" as xs e) = do
  let trs = HM.fromList [(int2Text i, tTy $ x ^. _2) | i <- [1 ..] | x <- xs]
  let vs' = HM.fromList [(x ^. _1, Reg (int2Text i)) | i <- [1 ..] | x <- xs]
  is <-
    local
      ( (vals <>~ vs')
          . (tCtx .~ HS.fromList as)
          . (tRegFile .~ trs)
      )
      $ tExp e
  pure $ Code as trs is
tHVal (M.Tuple vs) = Tuple <$> traverse tVal vs
tHVal h = error $ "not HVal: " <> T.unpack (prettyText h)


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
tExp (M.Let d e) = case d of
  M.Bind x v -> do
    r <- freshName
    v' <- tVal v
    is <-
      local
        ( (vals . at x ?~ Reg r)
            . (tRegFile . at r ?~ tTy (v ^. M.ty))
        )
        $ tExp e
    pure $ Mov r v' `Seq` is
  M.At x i v
    | M.TTuple ts <- v ^. M.ty -> do
        r <- freshName
        v' <- tVal v
        is <-
          local
            ( (vals . at x ?~ Reg r)
                . (tRegFile . at r ?~ tTy (ts ^?! ix (i - 1) . _1))
            )
            $ tExp e
        pure $ Mov r v' `Seq` Ld r r (i - 1) `Seq` is
    | otherwise ->
        error $ "At: t is not TTuple, but " <> T.unpack (prettyText $ v ^. M.ty)
  M.Arith x p v1 v2 -> do
    r <- freshName
    v1' <- tVal v1
    v2' <- tVal v2
    is <- local ((vals . at x ?~ Reg r) . (tRegFile . at r ?~ TInt)) $ tExp e
    pure $ Mov r v1' `Seq` Arith p r r v2' `Seq` is
  M.Unpack a x v@(_ `M.Ann` t)
    | M.TExists _b _t' <- t -> do
        r <- freshName
        v' <- tVal v
        is <-
          local
            ( (vals . at x ?~ Reg r)
                . (tCtx %~ HS.insert a)
                . (tRegFile . at r ?~ tTy t)
            )
            $ tExp e
        pure $ Unpack a r v' `Seq` is
    | otherwise -> error $ "t is not TExists, but " <> T.unpack (prettyText t)
  M.Malloc x ts -> do
    r <- freshName
    is <-
      local
        ( (vals . at x ?~ Reg r)
            . (tRegFile . at r ?~ TTuple (fmap (\t -> (tTy t, False)) ts))
        )
        $ tExp e
    pure $ Malloc r (fmap tTy ts) `Seq` is
  M.Update x v1 i v2
    | M.TTuple ts <- v1 ^. M.ty -> do
        r <- freshName
        v1' <- tVal v1
        r' <- freshName
        v2' <- tVal v2
        is <-
          local
            ( (vals . at x ?~ Reg r)
                . ( tRegFile
                      . at r
                      ?~ TTuple ((ts <&> _1 %~ tTy) & ix (i - 1) . _2 .~ True)
                  )
            )
            $ tExp e
        pure $ Mov r v1' `Seq` Mov r' v2' `Seq` St r (i - 1) r' `Seq` is
    | otherwise ->
        error $
          "Update: t is not TTuple, but " <> T.unpack (prettyText $ v1 ^. M.ty)
tExp (M.App v as vs) = do
  unless (null as) $ error "not (null as)"
  r0 <- freshName
  rs <- replicateM (length vs) freshName
  v' <- tVal v
  vs' <- traverse tVal vs
  pure $
    foldr Seq (Jmp $ Reg r0) $
      Mov r0 v'
        : [Mov r' v'' | r' <- rs | v'' <- vs']
          <> [Mov (T.pack $ show r) (Reg r') | r <- [(1 :: Int) ..] | r' <- rs]
tExp (M.If0 v e1 e2) = do
  r <- freshName
  l <- freshName
  is1 <- tExp e1
  is2 <- tExp e2
  v' <- tVal v
  tCtx' <- view tCtx
  trs <- view tRegFile
  tell $
    TalLog
      (HM.singleton l $ Code (HS.toList tCtx') trs is2)
      (HM.singleton l $ TCode (HS.toList tCtx') trs)
  pure $ Mov r v' `Seq` Bnz r (Label l) `Seq` is1
tExp (M.Halt t v) = do
  v' <- tVal v
  pure $ Mov "1" v' `Seq` Halt (tTy t)
