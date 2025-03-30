module SF2TAL.Middle.Tc
  ( ckTm
  )
where

import Control.Exception.Safe
import Control.Monad
import Data.Foldable
import Data.Map qualified as M
import Effectful
import Effectful.Reader.Static
import GHC.Stack
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import SF2TAL.Middle.Middle
import SF2TAL.Name
import SF2TAL.PP


type Env = M.Map Name Ty


data TcException where
  TcException :: HasCallStack => (PP.Doc ann) -> Env -> TcException


instance Show TcException where
  show (TcException e env) =
    docStr $ PP.vsep [e, "env:", ppMap ":" env, pp $ prettyCallStack callStack]


instance Exception TcException


type Tc ann es = (Reader Env :> es)


err :: (HasCallStack, Tc ann es) => [PP.Doc ann] -> Eff es a
err es = do
  env <- ask
  throwM $ TcException (PP.vsep es) env


lookupVar :: Tc ann es => Name -> Eff es Ty
lookupVar x = do
  env <- ask
  if
    | Just t <- env ^? ix x -> pure t
    | otherwise -> err ["Unbounded variable" <+> pp x]


ckTm :: Tm -> Eff es ()
ckTm e = runReader mempty do ckTm' e


ckTm' :: Tc ann es => Tm -> Eff es ()
ckTm' = \case
  Let d e -> do
    ckDecl d $ ckTm' e
    pure ()
  LetRec xs e -> do
    local (fmap tyOf xs <>) do
      traverse_ ckVal xs
      ckTm' e
  e@(App v bs vs) ->
    ckVal v >>= \case
      TFix as ts ->
        forM_ (zip ts vs) \(t, v') -> do
          let t' = foldr (uncurry tsubst) t (zip as bs)
          tv' <- ckVal v'
          when (t' /= tv') do
            err
              [ "Type of a argument does not match:" <+> pp v'
              , "expected:" <+> pp t'
              , "actual: " <+> pp tv'
              , pp e
              ]
      _ -> err ["Applying a non-function value", pp e]
  e@(If0 v e1 e2) -> do
    tv <- ckVal v
    when (tv /= TInt) do
      err ["Type of the condition is not int, but" <+> pp tv, pp e]
    _ <- ckTm' e1
    _ <- ckTm' e2
    pure ()
  Halt v -> void $ ckVal v
  Loc _ e -> ckTm' e


ckDecl :: Tc ann es => Decl -> Eff es a -> Eff es a
ckDecl d k = case d of
  Bind x v -> do
    tv <- ckVal v
    local (at x ?~ tv) k
  At x i v ->
    ckVal v >>= \case
      TTuple ts ->
        if
          | Just (t, _i) <- ts ^? ix (i - 1) -> local (at x ?~ t) k
          | otherwise -> err ["Invalid index", pp d]
      t -> err ["Indexing a non-tuple value:" <+> pp t, pp d]
  Arith x _p v1 v2 -> do
    tv1 <- ckVal v1
    tv2 <- ckVal v2
    when (tv1 /= TInt) do err ["LHS is not int, but" <+> pp tv1, pp d]
    when (tv2 /= TInt) do err ["RHS is not int, but" <+> pp tv2, pp d]
    local (at x ?~ TInt) k
  Unpack a x v ->
    ckVal v >>= \case
      TExists a' t -> local (at x ?~ tsubst a' (TVar a) t) k
      t -> err ["Unpacking non-existential value:" <+> pp t, pp d]
  Malloc x ts -> local (at x ?~ tTupleUninited ts) k
  Update x v1 i v2 -> do
    tv1 <- ckVal v1
    case tv1 of
      TTuple ts ->
        if
          | Just (t, _) <- ts ^? ix (i - 1) -> do
              tv2 <- ckVal v2
              when (tv2 /= t) do
                err
                  [ "Type of setting value does not match"
                  , "expected:" <+> pp t
                  , "actual:" <+> pp tv2
                  , pp d
                  ]
              local (at x ?~ tTupleInitN i tv1) k
          | otherwise -> err ["Invalid index", pp d]
      _ -> err ["Updating a non-tuple value: " <+> pp tv1, pp d]


ckVal :: Tc ann es => Val -> Eff es Ty
ckVal v = do
  t <- case v of
    Var x t -> do
      t' <- lookupVar x
      if t == t'
        then pure t
        else err ["Type of annotation does not match:" <+> pp t', pp v]
    IntLit _ -> pure TInt
    Abs as xs e ->
      let t = TFix as (fmap (^. _2) xs)
      in local (M.fromList xs <>) do
          _ <- ckTm' e
          pure t
    Tuple vs -> TTuple . fmap (,True) <$> mapM ckVal vs
    v' `AppT` t ->
      ckVal v' >>= \case
        TFix (a : as) ts ->
          pure $ TFix as (tsubst a t <$> ts)
        _ -> err ["Applying non-polymorphism value", pp v]
    Pack _t1 _v t2 ->
      pure t2

  if t == tyOf v
    then pure t
    else error "ty: type does not match"
