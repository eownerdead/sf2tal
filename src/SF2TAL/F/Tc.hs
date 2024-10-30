module SF2TAL.F.Tc
  ( ty
  )
where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map qualified as M
import Data.Text as T
import Lens.Micro.Platform
import SF2TAL.F.F


type Env = M.Map Name Ty


type Tc = ReaderT Env (Either T.Text)


extendEnv :: Name -> Ty -> Tc a -> Tc a
extendEnv x t = local do M.insert x t


ty :: Tm -> Either T.Text Tm
ty e = (`runReaderT` mempty) do ty' e


ty' :: Tm -> Tc Tm
ty' (Var x) = do
  env <- ask
  case env ^? ix x of
    Just t -> pure $ Var x `Ann` t
    Nothing -> throwError $ "Unbound variable " <> x
ty' (IntLit i) = pure $ Ann (IntLit i) TInt
ty' (Fix x x1 t1 t2 e) = do
  e' <- extendEnv x (t1 `TFun` t2) do extendEnv x1 t1 do ty' e
  when (ann e' /= t2) do throwError "Fix: e is not t2"
  pure $ Fix x x1 t1 t2 e' `Ann` (t1 `TFun` t2)
ty' (e1 `App` e2) = do
  e1' <- ty' e1
  e2' <- ty' e2
  if
    | t1 `TFun` t2 <- ann e1' -> do
        when (ann e2' /= t1) do throwError "App: Type not match"
        pure $ (e1' `App` e2') `Ann` t2
    | otherwise -> throwError "App: e1 is not TFun"
ty' (AbsT a e) = do
  e' <- ty' e
  pure $ AbsT a e' `Ann` TForall a (ann e')
ty' (e `AppT` t) = do
  e' <- ty' e
  if
    | TForall a t' <- ann e' -> pure $ (e' `AppT` t) `Ann` tsubst a t t'
    | otherwise -> throwError "AppT: e is not TForall"
ty' (Tuple es) = do
  es' <- traverse ty' es
  pure $ Tuple es' `Ann` TTuple (fmap ann es')
ty' (At i e) = do
  e' <- ty' e
  if
    | TTuple ts <- ann e', Just t <- ts ^? ix i -> pure $ At i e' `Ann` t
    | otherwise -> throwError "At: e is not TTuple or invalid i"
ty' (Arith p e1 e2) = do
  e1' <- ty' e1
  when (ann e1' /= TInt) do throwError "Arith: e1 is not TInt"
  e2' <- ty' e2
  when (ann e2' /= TInt) do throwError "Arith: e2 is not TInt"
  pure $ Arith p e1' e2' `Ann` TInt
ty' (If0 v e1 e2) = do
  v' <- ty' v
  when (ann v' /= TInt) do throwError "If0: v is not TInt"
  e1' <- ty' e1
  e2' <- ty' e2
  when (ann e1' /= ann e2') do throwError "If0: type of e1 and e2 is not same"
  pure $ If0 v' e1' e2' `Ann` ann e1'
ty' x@(_ `Ann` _) = error $ "Ann: " <> show x
