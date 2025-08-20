module SF2TAL.Llvm
  ( lProg
  )
where

import Data.Map qualified as M
import Data.Maybe
import Data.Text qualified as T
import Data.Text.Foreign qualified as T
import Data.Tuple
import Effectful
import Effectful.Reader.Static.Microlens
import Effectful.State.Static.Local.Microlens
import Foreign
import Lens.Micro.Platform hiding (preuse, preview, use, (%=), (?=))
import LlvmC.Raw.Core qualified as L
import LlvmC.Raw.Types qualified as L
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


type FunctionRef = L.ValueRef


functionType :: Bool -> L.TypeRef -> [L.TypeRef] -> IO L.TypeRef
functionType varargs tRet tParams =
  withArrayLen tParams \len ptr ->
    L.functionType tRet ptr (fromIntegral len) (L.Bool $ fromBool varargs)


structType :: Bool -> [L.TypeRef] -> IO L.TypeRef
structType packed' ts =
  withArrayLen ts \len ptr ->
    L.structType ptr (fromIntegral len) (L.Bool $ fromBool packed')


getParams :: FunctionRef -> IO [L.ValueRef]
getParams f = do
  len <- fromIntegral <$> L.countParams f
  allocaArray len \ptr -> do
    L.getParams f ptr
    peekArray len ptr


buildGEP2 ::
  L.BuilderRef ->
  L.TypeRef ->
  L.ValueRef ->
  [L.ValueRef] ->
  T.Text ->
  IO L.ValueRef
buildGEP2 b ty constantVal constantIndices name =
  withArrayLen constantIndices \len ptr ->
    T.withCString name $ L.buildGEP2 b ty constantVal ptr (fromIntegral len)


buildCall2 ::
  L.BuilderRef ->
  L.TypeRef ->
  L.ValueRef ->
  [L.ValueRef] ->
  T.Text ->
  IO L.ValueRef
buildCall2 b ty fn args name =
  withArrayLen args \len ptr ->
    T.withCString name $ L.buildCall2 b ty fn ptr (fromIntegral len)


addIncoming :: L.ValueRef -> [(L.ValueRef, L.BasicBlockRef)] -> IO ()
addIncoming b incoming =
  withArrayLen values \vlen vptr ->
    withArrayLen blocks \_blen bptr ->
      L.addIncoming b vptr bptr (fromIntegral vlen)
  where
    (values, blocks) = unzip incoming


lTy :: ToLlvm es => Ty -> Eff es L.TypeRef
lTy = \case
  TVar _ -> liftIO do
    t <- L.voidType
    L.pointerType t 0
  TInt -> liftIO L.int64Type
  TFix _as ts tk -> do
    ts' <- traverse lTy ts
    tk' <- lTy tk
    t <- liftIO $ functionType False tk' ts'
    -- t <- liftIO L.voidType
    liftIO $ L.pointerType t 0
  TTuple ts -> do
    t <- liftIO . structType True =<< traverse (lTy . fst) ts
    liftIO $ L.pointerType t 0
  TExists _a t -> lTy t


lTTuple :: ToLlvm es => Ty -> Eff es L.TypeRef
lTTuple = \case
  TTuple ts -> do
    liftIO . structType False =<< traverse (lTy . fst) ts
  _ -> error "TTuple expected"


lTFix :: ToLlvm es => Ty -> Eff es L.TypeRef
lTFix = \case
  TFix _as ts tk -> do
    ts' <- traverse lTy ts
    tk' <- lTy tk
    liftIO $ functionType False tk' ts'
  _ -> error "TFix expected"


lProg :: IOE :> es => Tm -> Eff es L.ModuleRef
lProg p = do
  m <- liftIO $ T.withCString "main" L.moduleCreateWithName
  evalState (LlvmState{phis = mempty}) $
    runReader (LlvmEnv{vars = mempty, conts = mempty}) do
      lProg' m p
  pure m


lProg' :: ToLlvm es => L.ModuleRef -> Tm -> Eff es ()
lProg' m = \case
  Let (Rec fs) e -> do
    fs' <- flip M.traverseWithKey fs \x (Abs _as xs _k tk _e1) -> do
      ts' <- traverse (lTy . snd) xs
      tk' <- lTy tk
      t' <- liftIO $ functionType False tk' ts'
      liftIO $ T.withCString (prettyText x) \str -> L.addFunction m str t'
    b <- liftIO L.createBuilder
    _ <- local (vars <>~ fs') do
      _ <- flip M.traverseWithKey fs \x (Abs _as xs _k _tk e1) -> do
        let f = fs' M.! x
        bb <- liftIO $ T.withCString "entry" $ L.appendBasicBlock f
        liftIO $ L.positionBuilderAtEnd b bb
        xs' <- liftIO $ getParams f
        local (vars <>~ M.fromList (zip (fmap fst xs) xs')) $ lExp b e1
      t <- liftIO $ L.int64Type >>= \ti -> functionType False ti []
      f <- liftIO $ T.withCString "sf2talMain" \str -> L.addFunction m str t
      bb <- liftIO $ T.withCString "entry" $ L.appendBasicBlock f
      liftIO $ L.positionBuilderAtEnd b bb
      lExp b e
    pure ()
  _ -> error "Top-level is not LetRec"


lVal :: ToLlvm es => Val -> Eff es L.ValueRef
lVal = \case
  Var x _t ->
    preview (vars . ix x) >>= \case
      Just x' -> pure x'
      Nothing -> error $ "undefined variable " <> T.unpack (prettyText x)
  IntLit i ->
    liftIO $
      L.int64Type >>= \t ->
        L.constInt t (fromIntegral i) (L.Bool 1)
  AppT v _ -> lVal v
  Pack _t1 v _t2 -> lVal v
  v -> error $ "not Val: " <> T.unpack (prettyText v)


lExp :: ToLlvm es => L.BuilderRef -> Tm -> Eff es ()
lExp b = \case
  Let d e -> case d of
    Bind x v -> do
      v' <- lVal v
      local (vars . at x ?~ v') do lExp b e
    BindK k x t e1 -> do
      f <- liftIO $ L.getBasicBlockParent =<< L.getInsertBlock b
      bb <- liftIO . T.withCString (prettyText k) $ L.appendBasicBlock f
      local (conts . at k ?~ bb) do lExp b e
      liftIO $ L.positionBuilderAtEnd b bb
      t' <- lTy t
      preuse (phis . ix k) >>= \case
        Just (M.toList -> [(_, v)]) -> local (vars . at x ?~ v) do lExp b e1
        Just phi -> do
          v <- liftIO $ T.withCString (prettyText x) $ L.buildPhi b t'
          liftIO $ addIncoming v (fmap swap $ M.toList phi)
          local (vars . at x ?~ v) do lExp b e1
        Nothing -> do
          lExp b e1
    At x i v
      | TTuple ts <- tyOf v
      , Just (tv, _) <- ts ^? ix (i - 1) -> do
          v' <- lVal v
          t <- lTTuple $ tyOf v
          i' <-
            liftIO $
              L.int64Type >>= \ti ->
                L.constInt ti (fromIntegral $ i - 1) (L.Bool 1)
          v'' <- liftIO $ buildGEP2 b t v' [i'] ""
          tv'' <- lTy tv
          v''' <-
            liftIO $ T.withCString (prettyText x) $ L.buildLoad2 b tv'' v''
          local (vars . at x ?~ v''') do lExp b e
      | otherwise ->
          error $ T.unpack $ "At: not TTuple, but " <> prettyText (tyOf v)
    Arith x p v1 v2 -> do
      v1' <- lVal v1
      v2' <- lVal v2
      let p' = case p of
            Add -> L.buildAdd
            Sub -> L.buildSub
            Mul -> L.buildMul
      v' <- liftIO $ T.withCString "" $ p' b v1' v2'
      local (vars . at x ?~ v') do lExp b e
    Unpack _a x v -> do
      v' <- lVal v
      local (vars . at x ?~ v') do lExp b e
    Malloc x ts -> do
      ts' <- liftIO . structType False =<< traverse lTy ts
      v' <- liftIO $ T.withCString (prettyText x) $ L.buildMalloc b ts'
      local (vars . at x ?~ v') do lExp b e
    Update x v1 i v2 -> do
      v1' <- lVal v1
      t <- lTTuple $ tyOf v1
      i' <-
        liftIO $
          L.int64Type >>= \ti ->
            L.constInt ti (fromIntegral $ i - 1) (L.Bool 1)
      v1'' <- liftIO $ buildGEP2 b t v1' [i'] ""
      v2' <- lVal v2
      _ <- liftIO $ L.buildStore b v2' v1''
      local (vars . at x ?~ v1') do lExp b e
    Rec _xs -> error "LetRec in non top-level"
  AppK k v -> do
    bbCur <- liftIO $ L.getInsertBlock b
    v' <- lVal v
    preview (conts . ix k) >>= \case
      Just bb -> do
        _ <- liftIO $ L.buildBr b bb
        phis . at k %= (Just . M.insert bbCur v' . fromMaybe mempty)
      Nothing -> do
        _ <- liftIO $ L.buildRet b v'
        pure ()
  App v _as vs k -> do
    bbCur <- liftIO $ L.getInsertBlock b
    v' <- lVal v
    tv' <- lTFix $ tyOf v
    vs' <- traverse lVal vs
    v'' <- liftIO $ buildCall2 b tv' v' vs' ""
    bb <- preview (conts . ix k)
    _ <- liftIO $ L.buildBr b (fromJust bb)
    phis . at k %= (Just . M.insert bbCur v'' . fromMaybe mempty)
  If0 v k1 k2 -> do
    v' <- lVal v
    i0 <- liftIO $ L.int64Type >>= \ti -> L.constInt ti 0 (L.Bool 1)
    cmp <-
      liftIO $
        T.withCString "cmp" $
          L.buildICmp b L.IntEQ v' i0
    bb1 <- fromJust <$> preview (conts . ix k1)
    bb2 <- fromJust <$> preview (conts . ix k2)
    _ <- liftIO $ L.buildCondBr b cmp bb1 bb2
    pure ()
  Halt v -> do
    v' <- lVal v
    _ <- liftIO $ L.buildRet b v'
    pure ()
  Loc _l e -> lExp b e
