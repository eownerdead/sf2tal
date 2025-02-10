module SF2TAL.Middle.Tc
  ( ckProg
  , ckTm
  )
where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map qualified as M
import Data.Text qualified as T
import Lens.Micro.Platform
import SF2TAL.Middle.Middle
import SF2TAL.Utils


type Env = M.Map Name Ty


type Tc = ReaderT Env (Either T.Text)


lookupVar :: Name -> Tc Ty
lookupVar x = do
  env <- ask
  if
    | Just t <- env ^? ix x -> pure t
    | otherwise -> throwError $ "unknown variable " <> int2Text x


ckProg :: Prog -> Either T.Text ()
ckProg p = runReaderT (ckProg' p) mempty


ckProg' :: Prog -> Tc ()
ckProg' (LetRec xs e) = local (fmap ty xs <>) do
  mapM_ ckVal xs
  ckTm' e


ckTm :: Tm -> Either T.Text ()
ckTm e = runReaderT (ckTm' e) mempty


ckTm' :: Tm -> Tc ()
ckTm' = \case
  Let d e -> do
    ckDecl d $ ckTm' e
    pure ()
  App v bs vs ->
    ckVal v >>= \case
      TFix as ts ->
        forM_ (zip ts vs) \(t, v') -> do
          let t' = foldr (uncurry tsubst) t (zip as bs)
          tv' <- ckVal v'
          if tv' == t'
            then pure ()
            else throwError $ "App: vs does not match: " <> prettyText tv'
      t -> throwError do
        "App: v is not TFix, but " <> prettyText t
  If0 v e1 e2 -> do
    tv <- ckVal v
    when (tv /= TInt) do
      throwError $ "If0: v is not TInt, but " <> prettyText tv
    _ <- ckTm' e1
    _ <- ckTm' e2
    pure ()
  Halt v -> void $ ckVal v


ckDecl :: Decl -> Tc a -> Tc a
ckDecl d k = case d of
  Bind x v -> do
    tv <- ckVal v
    local (at x ?~ tv) k
  At x i v ->
    ckVal v >>= \case
      TTuple ts | Just (t, _i) <- ts ^? ix (i - 1) -> do
        local (at x ?~ t) k
      t ->
        throwError $
          "At: v is not TTuple or invalid i: " <> prettyText t
  Arith x _p v1 v2 -> do
    tv1 <- ckVal v1
    tv2 <- ckVal v2
    when (tv1 /= TInt) do
      throwError $ "Arith: v1 is not TInt, but " <> prettyText tv1
    when (tv2 /= TInt) do
      throwError $ "Arith: v2 is not TInt, but " <> prettyText tv2
    local (at x ?~ TInt) k
  Unpack a x v ->
    ckVal v >>= \case
      TExists a' t -> do
        local (at x ?~ tsubst a' (TVar a) t) k
      t ->
        throwError $ "Unpack: v is not TExists, but " <> prettyText t
  Malloc x ts -> local (at x ?~ tTupleUninited ts) k
  Update x v1 i v2 -> do
    tv1 <- ckVal v1
    case tv1 of
      TTuple ts | Just (t, _) <- ts ^? ix (i - 1) -> do
        tv2 <- ckVal v2
        when (tv2 /= t) do
          throwError $
            "Update: type of v2 does not match: " <> prettyText tv2
        local (at x ?~ tTupleInitN i tv1) k
      _ ->
        throwError $
          "Update: v1 is not Tuple or invalid i: " <> prettyText tv1


ckVal :: Val -> Tc Ty
ckVal v = do
  t <- case v of
    Var x t -> do
      t' <- lookupVar x
      if t == t'
        then pure t
        else throwError $ "Var: " <> prettyText t'
    IntLit _ -> pure TInt
    Fix x as xs e ->
      let t = TFix as (fmap (^. _2) xs)
      in local (M.fromList xs <>) do
          local (maybe id (\x' -> at x' ?~ t) x) do
            _ <- ckTm' e
            pure t
    Tuple vs -> TTuple . fmap (,True) <$> mapM ckVal vs
    v' `AppT` t ->
      ckVal v' >>= \case
        TFix (a : as) ts ->
          pure $ TFix as (tsubst a t <$> ts)
        _ -> throwError "AppT: v is not TFix"
    Pack _t1 _v t2 ->
      pure t2

  if t == ty v
    then pure t
    else throwError "ckVal: Type does not match"
