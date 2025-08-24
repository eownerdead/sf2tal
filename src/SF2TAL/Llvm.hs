module SF2TAL.Llvm
  ( lProg
  )
where

import Control.Monad
import Data.Map qualified as M
import Data.Maybe
import Data.Text qualified as T
import Data.Tuple
import Effectful
import Effectful.Reader.Static.Microlens
import Effectful.State.Static.Local.Microlens
import Lens.Micro.Platform hiding (preuse, preview, use, (%=), (?=))
import LlvmC.Core qualified as L
import SF2TAL.Middle
import SF2TAL.PP
import SF2TAL.Utils


data LlvmEnv = LlvmEnv
  { vars :: M.Map Name L.ValueRef
  , conts :: M.Map KName L.BasicBlockRef
  }


newtype LlvmState = LlvmState
  { phis :: M.Map KName (M.Map L.BasicBlockRef L.ValueRef)
  }


$(makeFieldsId ''LlvmEnv)
$(makeFieldsId ''LlvmState)


type ToLlvm es =
  ( IOE :> es
  , Reader LlvmEnv :> es
  , State LlvmState :> es
  )


lTy :: (ToLlvm es, L.Context :> es) => Ty -> Eff es L.TypeRef
lTy = \case
  TVar _ -> L.pointerType 0
  TInt -> L.int64Type
  TFix{} -> L.pointerType 0
  TTuple{} -> L.pointerType 0
  TExists _a t -> lTy t


lTTuple :: (ToLlvm es, L.Context :> es) => Ty -> Eff es L.TypeRef
lTTuple = \case
  TTuple ts -> do
    L.structType False =<< traverse lTy ts
  _ -> error "TTuple expected"


lTFix :: (ToLlvm es, L.Context :> es) => Ty -> Eff es L.TypeRef
lTFix = \case
  TFix _as ts tk -> do
    ts' <- traverse lTy ts
    tk' <- lTy tk
    L.functionType False tk' ts'
  _ -> error "TFix expected"


lProg :: IOE :> es => Tm -> Eff es L.ModuleRef
lProg p = do
  L.runContext do
    ((), r) <- L.createModule "main" $
      evalState (LlvmState{phis = mempty}) $
        runReader (LlvmEnv{vars = mempty, conts = mempty}) do
          lProg' p
    pure r


lProg' :: (ToLlvm es, L.Module :> es, L.Context :> es) => Tm -> Eff es ()
lProg' = \case
  Let (Rec fs) e -> do
    fs' <- flip M.traverseWithKey fs \x (Abs _as xs _k tk _e1) -> do
      ts' <- traverse (lTy . snd) xs
      tk' <- lTy tk
      t' <- L.functionType False tk' ts'
      L.newFunction (prettyText x) t'
    _ <- local (vars <>~ fs') do
      _ <- flip M.traverseWithKey fs \x (Abs _as xs _k _tk e1) -> do
        let f = fs' M.! x
        L.defineFunction f \xs' -> do
          local (vars <>~ M.fromList (zip (fmap fst xs) xs')) $ lExp e1
      t <- L.int64Type >>= \ti -> L.functionType False ti []
      f <- L.newFunction "sf2talMain" t
      L.defineFunction f \_ -> do
        lExp e
    pure ()
  _ -> error "Top-level is not LetRec"


lVal :: (ToLlvm es, L.Context :> es) => Val -> Eff es L.ValueRef
lVal = \case
  Var x _t ->
    preview (vars . ix x) >>= \case
      Just x' -> pure x'
      Nothing -> error $ "undefined variable " <> T.unpack (prettyText x)
  IntLit i -> L.int64Type >>= \t -> L.constInt True t (fromIntegral i)
  AppT v _ -> lVal v
  Pack _t1 v _t2 -> lVal v


lExp :: (ToLlvm es, L.Context :> es, L.Builder :> es) => Tm -> Eff es ()
lExp = \case
  Let d e -> case d of
    Bind x v -> do
      v' <- lVal v
      local (vars . at x ?~ v') do lExp e
    BindK k x t e1 -> do
      t' <- lTy t
      f <- L.builderFunction
      bb <- L.appendBasicBlock (prettyText k) f
      local (conts . at k ?~ bb) do lExp e
      L.defineBasicBlock bb do
        preuse (phis . ix k) >>= \case
          Just (M.toList -> [(_, v)]) -> local (vars . at x ?~ v) do lExp e1
          Just phi -> do
            v <- L.buildPhi (prettyText x) t'
            L.addIncoming v (fmap swap $ M.toList phi)
            local (vars . at x ?~ v) do lExp e1
          Nothing -> do
            lExp e1
    At x i v
      | TTuple ts <- tyOf v
      , Just tv <- ts ^? ix (i - 1) -> do
          v' <- lVal v
          t <- lTTuple $ tyOf v
          i' <- L.int64Type >>= \ti -> L.constInt True ti (fromIntegral i - 1)
          v'' <- L.buildGEP2 "" t v' [i']
          tv'' <- lTy tv
          v''' <- L.buildLoad2 (prettyText x) tv'' v''
          local (vars . at x ?~ v''') do lExp e
      | otherwise ->
          error $ T.unpack $ "At: not TTuple, but " <> prettyText (tyOf v)
    BinOp x p v1 v2 -> do
      v1' <- lVal v1
      v2' <- lVal v2
      let icmp cmp = do
            v <- L.buildICmp "" cmp v1' v2'
            L.buildZExt "" v =<< L.int64Type
      v' <- case p of
        BAdd -> L.buildAdd "" v1' v2'
        BSub -> L.buildSub "" v1' v2'
        BMul -> L.buildMul "" v1' v2'
        BEq -> icmp L.IntEQ
        BNe -> icmp L.IntNE
        BLt -> icmp L.IntSLT
        BLe -> icmp L.IntSLE
      local (vars . at x ?~ v') do lExp e
    Unpack _a x v -> do
      v' <- lVal v
      local (vars . at x ?~ v') do lExp e
    CTuple x vs -> do
      ts' <- lTTuple $ TTuple $ fmap tyOf vs
      v' <- L.buildMalloc (prettyText x) ts'
      forM_ (zip vs [1 ..]) \(vi, i) -> do
        vi' <- lVal vi
        i' <- L.int64Type >>= \ti -> L.constInt True ti (i - 1)
        vd <- L.buildGEP2 "" ts' v' [i']
        L.buildStore vi' vd
      local (vars . at x ?~ v') do lExp e
    Rec _xs -> error "LetRec in non top-level"
  AppK k v -> do
    bbCur <- L.getInsertBlock
    v' <- lVal v
    preview (conts . ix k) >>= \case
      Just bb -> do
        _ <- L.buildBr bb
        phis . at k %= (Just . M.insert bbCur v' . fromMaybe mempty)
      Nothing -> do
        _ <- L.buildRet v'
        pure ()
  App v _as vs k -> do
    bbCur <- L.getInsertBlock
    v' <- lVal v
    tv' <- lTFix $ tyOf v
    vs' <- traverse lVal vs
    v'' <- L.buildCall2 "" tv' v' vs'
    bb <- preview (conts . ix k)
    _ <- L.buildBr (fromJust bb)
    phis . at k %= (Just . M.insert bbCur v'' . fromMaybe mempty)
  If v k1 k2 -> do
    v' <- lVal v
    i0 <- L.int64Type >>= \ti -> L.constInt True ti 0
    cmp <- L.buildICmp "cmp" L.IntNE v' i0
    bb1 <- fromJust <$> preview (conts . ix k1)
    bb2 <- fromJust <$> preview (conts . ix k2)
    _ <- L.buildCondBr cmp bb1 bb2
    pure ()
  Halt v -> do
    v' <- lVal v
    _ <- L.buildRet v'
    pure ()
  Loc _l e -> lExp e
