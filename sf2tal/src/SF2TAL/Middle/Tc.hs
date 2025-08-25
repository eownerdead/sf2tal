module SF2TAL.Middle.Tc
  ( ckTm
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


ckAbs :: Tc ann es => Abs -> Eff es Ty
ckAbs (Abs as xs k tk e) =
  local ((u_ <>~ M.fromList xs) . (k_ . at k ?~ tk)) do
    _ <- ckTm' e
    pure $ TFix as (fmap (^. _2) xs) tk


ckDecl :: Tc ann es => Decl -> Eff es a -> Eff es a
ckDecl d k = case d of
  Bind x v -> do
    tv <- ckVal v
    local (u_ . at x ?~ tv) k
  BindK x x1 t1 e1 -> do
    local (u_ . at x1 ?~ t1) do
      _ <- ckTm e1
      local (k_ . at x ?~ t1) k
  Rec xs -> do
    local (u_ <>~ fmap tyOf xs) do
      traverse_ ckAbs xs
      k
  At x i y ->
    case tyOf y of
      TTuple ts ->
        if
          | Just t <- ts ^? ix (i - 1) -> local (u_ . at x ?~ t) k
          | otherwise -> err ["Invalid index", pp d]
      t -> err ["Indexing a non-tuple value:" <+> pp t, pp d]
  BinOp x _p x1 x2 -> do
    when (tyOf x1 /= TInt) do err ["LHS is not int, but" <+> pp (tyOf x1), pp d]
    when (tyOf x2 /= TInt) do err ["RHS is not int, but" <+> pp (tyOf x2), pp d]
    local (u_ . at x ?~ TInt) k
  Unpack a x y ->
    case tyOf y of
      TExists a' t -> local (u_ . at x ?~ tsubst a' (TVar a) t) k
      t -> err ["Unpacking non-existential value:" <+> pp t, pp d]
  CTuple x vs -> local (u_ . at x ?~ TTuple (fmap tyOf vs)) k


ckTm' :: Tc ann es => Tm -> Eff es ()
ckTm' = \case
  Let d e -> do
    ckDecl d $ ckTm' e
    pure ()
  AppK _k _x -> pure ()
  e@(App x bs xs _k) ->
    case tyOf x of
      TFix as ts _tk ->
        forM_ (zip ts xs) \(t1, x1) -> do
          let t' = foldr (uncurry tsubst) t1 (zip as bs)
          when (t' /= tyOf x1) do
            err
              [ "Type of a argument does not match:" <+> pp x1
              , "expected:" <+> pp t'
              , "actual: " <+> pp (tyOf x1)
              , pp e
              ]
      _ -> err ["Applying a non-function value", pp e]
  e@(If x _k1 _k2) -> do
    when (tyOf x /= TInt) do
      err ["Type of the condition is not int, but" <+> pp (tyOf x), pp e]
  Halt _ -> pure ()
  Loc _ e -> ckTm' e


ckTm :: Tm -> Eff es ()
ckTm e = runReader (Env{u_ = mempty, k_ = mempty}) do ckTm' e
