module SF2TAL.Middle.Opt
  ( oTopLevel
  )
where

import Data.Map qualified as M
import Effectful.Reader.Static.Microlens
import Effectful.State.Static.Local.Microlens
import SF2TAL.Middle.Middle
import SF2TAL.Prelude


data DEnv = DEnv
  { tsubsts :: M.Map TName Ty
  , substs :: M.Map Name Val
  }


newtype DAcc = DAcc
  { occurs :: M.Map Name Int
  }


$(makeFieldsId 'DEnv)
$(makeFieldsId 'DAcc)


type Opt es = (Reader DEnv :> es, State DAcc :> es)


oVal :: Opt es => Val -> Eff es Val
oVal = \case
  Var x t ->
    preview (substs . ix x) >>= \case
      Just v -> pure v
      Nothing -> do
        occurs . at x %= \case
          Just n -> Just $ n + 1
          Nothing -> Just 1
        pure $ Var x t
  IntLit i -> pure $ IntLit i
  AppT v t -> do
    v' <- oVal v
    pure $ AppT v' t
  Pack t1 v t2 -> do
    v' <- oVal v
    pure $ Pack t1 v' t2


rebuildLet :: Opt es => Name -> Decl -> Tm -> Eff es Tm
rebuildLet x d e = do
  e' <-
    preuse (occurs . ix x) <&> \case
      Just _ -> Let d e
      Nothing -> e
  occurs . at x .= Nothing
  pure e'


evalBinOp :: BinOps -> Int -> Int -> Int
evalBinOp p i1 i2 = case p of
  BAdd -> i1 + i2
  BSub -> i1 - i2
  BMul -> i1 * i2
  BEq -> fromEnum $ i1 == i2
  BNe -> fromEnum $ i1 /= i2
  BLt -> fromEnum $ i1 < i2
  BLe -> fromEnum $ i1 <= i2


oTm :: Opt es => Tm -> Eff es Tm
oTm = \case
  Let (Bind x v) e -> do
    v' <- oVal v
    local (substs . at x ?~ v') do oTm e
  Let (Rec ds) e -> do
    ds' <- oHVal ds
    e' <- oTm e
    occurs %= (M.\\ ds)
    pure $ Let (Rec ds') e'
  Let (BindK k x t e1) e -> do
    e' <- oTm e
    x' <- preuse (occurs . ix x)
    e1' <- oTm e1
    occurs . at x .= x'
    pure $ Let (BindK k x t e1') e'
  Let (At x i v) e -> do
    v' <- oVal v
    e' <- oTm e
    rebuildLet x (At x i v') e'
  Let (BinOp x p v1 v2) e -> do
    v1' <- oVal v1
    v2' <- oVal v2
    e' <- case (v1', v2') of
      (IntLit i1, IntLit i2) ->
        local (substs . at x ?~ IntLit (evalBinOp p i1 i2)) $ oTm e
      _ -> oTm e
    rebuildLet x (BinOp x p v1' v2') e'
  Let (Unpack a x v) e -> do
    oVal v >>= \case
      Pack t1 v' _t2 -> do
        local ((substs . at x ?~ v') . (tsubsts . at a ?~ t1)) do oTm e
      v' -> do
        e' <- oTm e
        occurs . at x .= Nothing
        pure $ Let (Unpack a x v') e'
  k `AppK` v -> (k `AppK`) <$> oVal v
  App v ts vs k -> do
    v' <- oVal v
    vs' <- traverse oVal vs
    pure $ App v' ts vs' k
  If v k1 k2 -> do
    oVal v <&> \case
      IntLit 0 -> k2 `AppK` IntLit 0
      IntLit _ -> k1 `AppK` IntLit 0
      v' -> If v' k1 k2
  Meta m e -> Meta m <$> oTm e


oHVal :: Opt es => M.Map Name Data -> Eff es (M.Map Name Data)
oHVal ds = do
  ds' <- forM ds \case
    Abs as xs k tk e1 -> do
      e1' <- oTm e1
      occurs %= (M.\\ M.fromList xs)
      pure $ Abs as xs k tk e1'
    Tuple vs -> Tuple <$> traverse oVal vs
  pure ds'


oTopLevel :: TopLevel -> Eff es TopLevel
oTopLevel (TopLevel ds) = runReader (DEnv{tsubsts = mempty, substs = mempty}) $
  evalState (DAcc{occurs = mempty}) do TopLevel <$> oHVal ds
