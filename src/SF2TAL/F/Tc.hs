module SF2TAL.F.Tc
  ( ty
  )
where

import Control.Exception.Safe
import Control.Monad
import Data.Map qualified as M
import Effectful
import Effectful.Reader.Static
import GHC.Stack
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import SF2TAL.F.F
import SF2TAL.PP


type Env = M.Map Name Ty


data TcException where
  TcException :: HasCallStack => PP.Doc ann -> TcException


instance Show TcException where
  show (TcException e) = docStr $ PP.vsep [e, pp $ prettyCallStack callStack]


instance Exception TcException


type Tc ann es = (Reader Env :> es)


err :: (HasCallStack, Tc ann es) => PP.Doc ann -> Eff es a
err = throwM . TcException


extendEnv :: Tc ann es => Name -> Ty -> Eff es a -> Eff es a
extendEnv x t = local do M.insert x t


ty :: Tm -> Eff es Tm
ty e = runReader mempty do ty' e


ty' :: Tc ann es => Tm -> Eff es Tm
ty' = \case
  Var x -> do
    env <- ask
    case env ^? ix x of
      Just t -> pure $ Var x `Ann` t
      Nothing -> err $ "Unbound variable " <> pp x
  IntLit i -> pure $ Ann (IntLit i) TInt
  Fix x x1 t1 t2 e -> do
    e' <- extendEnv x (t1 `TFun` t2) do extendEnv x1 t1 do ty' e
    when (ann e' /= t2) do err "Fix: e is not t2"
    pure $ Fix x x1 t1 t2 e' `Ann` (t1 `TFun` t2)
  e1 `App` e2 -> do
    e1' <- ty' e1
    e2' <- ty' e2
    if
      | t1 `TFun` t2 <- ann e1' -> do
          when (ann e2' /= t1) do err "App: Type not match"
          pure $ (e1' `App` e2') `Ann` t2
      | otherwise -> err "App: e1 is not TFun"
  AbsT a e -> do
    e' <- ty' e
    pure $ AbsT a e' `Ann` TForall a (ann e')
  e `AppT` t -> do
    e' <- ty' e
    if
      | TForall a t' <- ann e' -> pure $ (e' `AppT` t) `Ann` tsubst a t t'
      | otherwise -> err "AppT: e is not TForall"
  Tuple es -> do
    es' <- traverse ty' es
    pure $ Tuple es' `Ann` TTuple (fmap ann es')
  At i e -> do
    e' <- ty' e
    if
      | TTuple ts <- ann e', Just t <- ts ^? ix i -> pure $ At i e' `Ann` t
      | otherwise -> err "At: e is not TTuple or invalid i"
  Arith p e1 e2 -> do
    e1' <- ty' e1
    when (ann e1' /= TInt) do err "Arith: e1 is not TInt"
    e2' <- ty' e2
    when (ann e2' /= TInt) do err "Arith: e2 is not TInt"
    pure $ Arith p e1' e2' `Ann` TInt
  If0 v e1 e2 -> do
    v' <- ty' v
    when (ann v' /= TInt) do err "If0: v is not TInt"
    e1' <- ty' e1
    e2' <- ty' e2
    when (ann e1' /= ann e2') do err "If0: type of e1 and e2 is not same"
    pure $ If0 v' e1' e2' `Ann` ann e1'
  x@(_ `Ann` _) -> error $ "Ann: " <> show x
