module SF2TAL.Middle.Tc
  ( ckTopLevel
  , ckTm
  )
where

import Data.Map qualified as M
import Effectful.Reader.Static
import Prettyprinter qualified as PP
import SF2TAL.Middle.Middle
import SF2TAL.PP
import SF2TAL.Prelude


data Env = Env
  { u_ :: M.Map Name Ty
  , k_ :: M.Map KName Ty
  }


$(makeFieldsId ''Env)


data TcException where
  TcException ::
    HasCallStack =>
    (PP.Doc ann) ->
    Env ->
    TcException


instance Show TcException where
  show (TcException e env) =
    docStr $
      PP.vsep
        [ e
        , "env:"
        , ppMap ":" (env ^. u_)
        , "kenv:"
        , ppMap ":" (env ^. k_)
        , pp $ prettyCallStack callStack
        ]


instance Exception TcException


type Tc ann es = (Reader Env :> es)


err :: (HasCallStack, Tc ann es) => [PP.Doc ann] -> Eff es a
err es = do
  env <- ask
  throwIO $ TcException (PP.vsep es) env


lookupVar :: Tc ann es => Name -> Eff es Ty
lookupVar x = do
  env <- ask
  if
    | Just t <- env ^? u_ . ix x -> pure t
    | otherwise -> err ["Unbounded variable" <+> pp x]


ckVal :: Tc ann es => Val -> Eff es Ty
ckVal v = do
  t <- case v of
    Var x t -> do
      t' <- lookupVar x
      if t == t'
        then pure t
        else err ["Type of annotation does not match:" <+> pp t', pp v]
    IntLit _ -> pure TInt
    v' `AppT` t ->
      ckVal v' >>= \case
        TFix (a : as) ts tk ->
          pure $ TFix as (tsubst a t <$> ts) tk
        _ -> err ["Applying non-polymorphism value", pp v]
    Pack _t1 _v t2 ->
      pure t2

  if t == tyOf v
    then pure t
    else error "ty: type does not match"


ckData :: Tc ann es => Data -> Eff es Ty
ckData = \case
  Abs as xs k tk e ->
    local ((u_ <>~ M.fromList xs) . (k_ . at k ?~ tk)) do
      _ <- ckTm e
      pure $ TFix as (fmap (^. _2) xs) tk
  Tuple vs -> pure $ TTuple $ fmap tyOf vs


ckTm' :: Tc ann es => Tm -> Eff es ()
ckTm' expr = case expr of
  Let (Bind x v) e -> do
    _ <- ckVal v
    local (u_ . at x ?~ tyOf v) do ckTm' e
  Let (Rec xs) e -> do
    let ts = fmap tyOf xs
    local (u_ <>~ fmap tyOf xs) do
      ts' <- traverse ckData xs
      when (ts /= ts') $
        err
          [ "Type of rec does not match"
          , pp expr
          , "expected:" <+> ppMap ":" ts
          , "actual:" <+> ppMap ":" ts'
          ]
      ckTm' e
  Let (BindK x x1 t1 e1) e -> do
    local (u_ . at x1 ?~ t1) do
      _ <- ckTm' e1
      local (k_ . at x ?~ t1) $ ckTm' e
  Let (At x i y) e ->
    case tyOf y of
      TTuple ts ->
        if
          | Just t <- ts ^? ix (i - 1) -> local (u_ . at x ?~ t) $ ckTm' e
          | otherwise -> err ["Invalid index", pp expr]
      t -> err ["Indexing a non-tuple value:" <+> pp t, pp expr]
  Let (BinOp x _p x1 x2) e -> do
    when (tyOf x1 /= TInt) do err ["LHS is not int, but" <+> pp (tyOf x1), pp expr]
    when (tyOf x2 /= TInt) do err ["RHS is not int, but" <+> pp (tyOf x2), pp expr]
    local (u_ . at x ?~ TInt) $ ckTm' e
  Let (Unpack a x y) e ->
    case tyOf y of
      TExists a' t -> local (u_ . at x ?~ tsubst a' (TVar a) t) $ ckTm' e
      t -> err ["Unpacking non-existential value:" <+> pp t, pp expr]
  AppK _k _x -> pure ()
  App x bs xs _k ->
    case tyOf x of
      TFix as ts _tk ->
        forM_ (zip ts xs) \(t1, x1) -> do
          let t' = foldr (uncurry tsubst) t1 (zip as bs)
          when (t' /= tyOf x1) do
            err
              [ "Type of a argument does not match:" <+> pp x1
              , "expected:" <+> pp t'
              , "actual: " <+> pp (tyOf x1)
              , pp expr
              ]
      _ -> err ["Applying a non-function value", pp expr]
  If x _k1 _k2 -> do
    when (tyOf x /= TInt) do
      err ["Type of the condition is not int, but" <+> pp (tyOf x), pp expr]
  Meta _ e -> ckTm' e


ckTm :: Tm -> Eff es ()
ckTm e = runReader (Env{u_ = mempty, k_ = mempty}) do
  ckTm' e


ckTopLevel :: TopLevel -> Eff es ()
ckTopLevel (TopLevel fs) = runReader (Env{u_ = mempty, k_ = mempty}) do
  traverse_ ckData fs
