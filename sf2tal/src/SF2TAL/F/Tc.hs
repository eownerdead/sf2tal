module SF2TAL.F.Tc
  ( ck
  )
where

import Data.Map qualified as M
import Effectful.Reader.Static.Microlens
import Prettyprinter qualified as PP
import SF2TAL.F.F
import SF2TAL.PP
import SF2TAL.Prelude


data Env = Env
  { env :: M.Map Name Ty
  , curSpan :: Position
  }


$(makeFieldsId ''Env)


data TcException where
  TcException :: HasCallStack => PP.Doc ann -> Env -> TcException


instance Show TcException where
  show (TcException e env') =
    docStr $
      PP.vsep
        [ e
        , "at:" <+> pp (env' ^. curSpan)
        , "env:"
        , ppMap ":" (env' ^. env)
        , pp $ prettyCallStack callStack
        ]


instance Exception TcException


type Tc ann es = (Reader Env :> es)


err :: (HasCallStack, Tc ann es) => [PP.Doc ann] -> Eff es a
err es = do
  env' <- ask
  throwIO $ TcException (PP.vsep es) env'


ck :: Tm -> Eff es ()
ck = runReader (Env{env = mempty, curSpan = def}) . void . ck'


ck' :: Tc ann es => Tm -> Eff es Ty
ck' e = do
  t <- case e of
    Var x (Just t) -> do
      preview (env . ix x) >>= \case
        Just t'
          | t == t' -> pure t
          | otherwise ->
              err ["Type of variable annotation does not match:" <+> pp t', pp e]
        Nothing -> err ["Unbound variable", pp e]
    Var _ Nothing -> err ["Unannotated variable", pp e]
    IntLit _ -> pure TInt
    LetRec (Decls _ts es) e' ->
      local (env <>~ fmap tyOf es) do
        traverse_ ck' es
        ck' e'
    Abs x1 (Just t1) e' -> do
      t2 <- local (env . at x1 ?~ t1) do ck' e'
      pure $ t1 `TFun` t2
    Abs _ Nothing _ -> err ["Unannotated abstraction", pp e]
    e1 `App` e2 -> do
      t1 <- ck' e1
      t2 <- ck' e2
      if
        | s1 `TFun` s2 <- t1 -> do
            when (t2 /= s1) do
              err
                [ "Type of argument does not match"
                , "expected:" <+> pp t2
                , "actual:" <+> pp s1
                , pp e
                ]
            pure s2
        | otherwise -> err ["Applying non-function value", pp e]
    AbsT a e' -> TForall a <$> ck' e'
    e' `AppT` t -> do
      ck' e' >>= \case
        TForall a t' -> pure $ tsubst a t t'
        _ -> err ["Applying non-polymorphism value", pp e]
    Tuple es -> TTuple <$> traverse ck' es
    At i e' -> do
      ck' e' >>= \case
        TTuple ts ->
          if
            | Just t' <- ts ^? ix (i - 1) -> pure t'
            | otherwise -> err ["Invalid index", pp e]
        t -> err ["Indexing a non-tuple value:" <+> pp t, pp e]
    BinOp _ e1 e2 -> do
      t1 <- ck' e1
      when (t1 /= TInt) do err ["LHS is not int, but" <+> pp t1, pp e]
      t2 <- ck' e2
      when (t2 /= TInt) do err ["RHS is not int, but" <+> pp t2, pp e]
      pure TInt
    If v e1 e2 -> do
      tv <- ck' v
      when (tv /= TInt) do err ["Type of the condition is not int, but" <+> pp tv, pp e]
      t1 <- ck' e1
      t2 <- ck' e2
      when (t1 /= t2) do
        err ["then and else is not a same", "then:" <+> pp t1, "else:" <+> pp t2, pp e]
      pure t1
    x@(_ `Ann` _) -> err ["Ann:" <+> pp x]
    Meta (Span s) e' -> local (curSpan .~ s) do ck' e'

  if t == tyOf e
    then pure t
    else err ["expected:" <+> pp t, "tyOf:" <+> pp (tyOf e), pp e]
