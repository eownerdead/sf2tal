module SF2TAL.Middle.Tc
  ( ckProg
  , ckTm
  )
where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.HashMap.Strict qualified as HM
import Data.Text qualified as T
import Lens.Micro.Platform
import SF2TAL.Middle.Middle
import SF2TAL.Utils


type Env = HM.HashMap Name Ty


type Tc = ReaderT Env (Either T.Text)


lookupVar :: Name -> Tc Ty
lookupVar x = do
  env <- ask
  if
    | Just t <- env ^? ix x -> pure t
    | otherwise -> throwError $ "unknown variable " <> x


ckProg :: Prog -> Either T.Text ()
ckProg p = runReaderT (ckProg' p) mempty


ckProg' :: Prog -> Tc ()
ckProg' (LetRec xs e) = local (fmap (^. ty) xs <>) $ do
  mapM_ ckAnn xs
  ckTm' e


ckTm :: Tm -> Either T.Text ()
ckTm e = runReaderT (ckTm' e) mempty


ckTm' :: Tm -> Tc ()
ckTm' (Let d e) = do
  ckDecl d $ ckTm' e
ckTm' (App v bs vs)
  | TFix as ts <- v ^. ty = forM_ (zip ts vs) $ \(t, v') -> do
      let t' = foldr (uncurry tsubst) t (zip as bs)
      when (v' ^. ty /= t') $
        throwError $
          "App: vs does not match: " <> prettyText (v' ^. ty)
  | otherwise = throwError $ "App: v is not TFix, but " <> prettyText (v ^. ty)
ckTm' (If0 v e1 e2) = do
  when (v ^. ty /= TInt) $
    throwError $
      "If0: v is not TInt, but " <> prettyText (v ^. ty)
  ckTm' e1
  ckTm' e2
ckTm' (Halt t v) =
  when (v ^. ty /= t) $
    throwError $
      "Halt: v is not t, but " <> prettyText (v ^. ty)


ckDecl :: Decl -> Tc a -> Tc a
ckDecl (Bind x v) k = do
  ckAnn v
  local (at x ?~ v ^. ty) k
ckDecl (At x i v) k
  | TTuple ts <- v ^. ty
  , Just t <- ts ^? ix (i - 1) = do
      ckAnn v
      local (at x ?~ fst t) k
  | otherwise =
      throwError $ "At: v is not TTuple or invalid i: " <> prettyText (v ^. ty)
ckDecl (Arith x _p v1 v2) k = do
  ckAnn v1
  ckAnn v2
  when (v1 ^. ty /= TInt) $
    throwError $
      "Arith: v1 is not TInt, but " <> prettyText (v1 ^. ty)
  when (v2 ^. ty /= TInt) $
    throwError $
      "Arith: v2 is not TInt, but " <> prettyText (v2 ^. ty)
  local (at x ?~ TInt) k
ckDecl (Unpack a x v) k
  | TExists a' t <- v ^. ty = do
      ckAnn v
      local (at x ?~ tsubst a' (TVar a) t) k
  | otherwise =
      throwError $ "Unpack: v is not TExists, but " <> prettyText (v ^. ty)
ckDecl (Malloc x ts) k = local (at x ?~ tTupleUninited ts) k
ckDecl (Update x v1 i v2) k
  | TTuple ts <- v1 ^. ty
  , Just (t, _) <- ts ^? ix (i - 1) = do
      ckAnn v1
      ckAnn v2
      when (v2 ^. ty /= t) $
        throwError $
          "Update: type of v2 does not match: " <> prettyText (v2 ^. ty)
      local (at x ?~ tTupleInitN i (v1 ^. ty)) k
  | otherwise =
      throwError $
        "Update: v1 is not Tuple or invalid i: " <> prettyText (v1 ^. ty)


ckAnn :: Ann -> Tc ()
ckAnn (u `Ann` t) = case u of
  Var x -> do
    t' <- lookupVar x
    when (t /= t') $
      throwError $
        "Var: Ann: " <> prettyText u
  IntLit _ ->
    when (t /= TInt) $
      throwError $
        "IntLit: Ann is not TInt, but " <> prettyText t
  Fix x _as xs e ->
    if
      | TFix _as' _ts <- t ->
          local ((HM.fromList xs & at x ?~ t) <>) $ ckTm' e
      | otherwise -> throwError $ "Fix: Ann is not TFix, but " <> prettyText t
  Tuple vs -> do
    mapM_ ckAnn vs
    when (tTuple (fmap (^. ty) vs) /= t) $
      throwError $
        "Tuple: Ann not match: " <> prettyText t
  v `AppT` t' ->
    if
      | TFix (a : as) ts <- v ^. ty -> do
          ckAnn v
          when (TFix as (tsubst a t' <$> ts) /= t) $
            throwError $
              "AppT: Ann not match: " <> prettyText t
      | otherwise -> throwError $ "AppT: v is not TFix, but " <> prettyText t
  Pack t1 v t2 ->
    if
      | TExists a t2' <- t2 -> do
          ckAnn v
          when (t2 /= t) $ throwError $ "Pack: Ann not match: " <> prettyText t
          when (v ^. ty /= tsubst a t1 t2') $
            throwError $
              "Pack: Invalid v: " <> prettyText (tsubst a t1 t2')
      | otherwise ->
          throwError $ "Pack: t2 is not TExists, but " <> prettyText t2
