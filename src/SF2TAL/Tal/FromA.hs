module SF2TAL.Tal.FromA (tProg) where

import Control.Monad
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Effectful
import Effectful.Labeled
import Effectful.Reader.Static
import Effectful.Reader.Static.Microlens
import Effectful.Writer.Static.Local
import Lens.Micro.Platform hiding (preview, view)
import SF2TAL.Middle qualified as M
import SF2TAL.Tal.Tal
import SF2TAL.Uniq
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


type Tal es =
  ( Uniq :> es
  , Reader TalEnv :> es
  , Labeled "heaps" (Writer Heaps) :> es
  , Labeled "tHeap" (Writer THeap) :> es
  )


tProg :: Uniq :> es => M.Prog -> Eff es (Prog, THeap)
tProg p = do
  ((is, ths), hs) <- runReader TalEnv{vals = mempty, tCtx = mempty, tRegFile = mempty} $
    runLabeled @"heaps" runWriter $ runLabeled @"tHeap" runWriter do
      tProg' p
  pure (Prog hs mempty is, ths)


tProg' :: Tal es => M.Prog -> Eff es Seq
tProg' (M.LetRec xs e) = do
  vs <- traverse (const fresh) xs
  local (vals .~ fmap Label vs) do
    hs' <- traverse tHVal $ M.mapKeys (vs M.!) xs
    is <- tExp e
    labeled @"heaps" $ tell hs'
    labeled @"tHeap" $ tell $ fmap (tTy . M.ty) $ M.mapKeys (vs M.!) xs
    pure is


tHVal :: Tal es => M.Val -> Eff es HVal
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


tVal :: Tal es => M.Val -> Eff es Val
tVal = \case
  M.Var x _t ->
    preview (vals . ix x) >>= \case
      Just x' -> pure x'
      Nothing -> error $ "undefined variable " <> T.unpack (prettyText x)
  M.IntLit i -> pure $ IntLit i
  M.AppT v s -> AppT <$> tVal v <*> pure (tTy s)
  M.Pack t1 v t2 -> Pack (tTy t1) <$> tVal v <*> pure (tTy t2)
  v -> error $ "not Val: " <> T.unpack (prettyText v)


tExp :: Tal es => M.Tm -> Eff es Seq
tExp = \case
  M.Let d e -> case d of
    M.Bind x v -> do
      r <- R <$> fresh
      v' <- tVal v
      is <-
        local
          do (vals . at x ?~ Reg r) . (tRegFile . at r ?~ tTy (M.ty v))
          do tExp e
      pure $ Mov r v' `Seq` is
    M.At x i v
      | M.TTuple ts <- M.ty v -> do
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
            "At: t is not TTuple, but " <> T.unpack (prettyText $ M.ty v)
    M.Arith x p v1 v2 -> do
      r <- R <$> fresh
      v1' <- tVal v1
      v2' <- tVal v2
      is <-
        local
          do (vals . at x ?~ Reg r) . (tRegFile . at r ?~ TInt)
          do tExp e
      pure $ Mov r v1' `Seq` Arith p r r v2' `Seq` is
    M.Unpack a x v
      | M.TExists _b _t' <- M.ty v -> do
          r <- R <$> fresh
          v' <- tVal v
          is <-
            local
              do
                (vals . at x ?~ Reg r)
                  . (tCtx %~ S.insert a)
                  . (tRegFile . at r ?~ tTy (M.ty v))
              do tExp e
          pure $ Unpack a r v' `Seq` is
      | otherwise ->
          error $ "t is not TExists, but " <> T.unpack (prettyText (M.ty v))
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
      | M.TTuple ts <- M.ty v1 -> do
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
            "Update: t is not TTuple, but " <> T.unpack (prettyText $ M.ty v1)
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
    labeled @"heaps" $ tell do M.singleton l $ Code (S.toList tCtx') trs is2
    labeled @"tHeap" $ tell do M.singleton l $ TCode (S.toList tCtx') trs
    pure $ Mov r v' `Seq` Bnz r (Label l) `Seq` is1
  M.Halt v -> do
    v' <- tVal v
    pure $ Mov (A 1) v' `Seq` Halt (tTy (M.ty v))
