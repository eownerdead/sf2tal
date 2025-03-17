module SF2TAL.F.F
  ( TName
  , Ty (..)
  , SubTys (..)
  , ftv
  , tsubst
  , Tm (..)
  , tyOf
  , Prim (..)
  )
where

import Data.Map qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import SF2TAL.Name
import SF2TAL.PP


type TName = T.Text


-- | t
data Ty where
  -- | a
  TVar :: TName -> Ty
  -- | int
  TInt :: Ty
  -- | t1 -> t2
  TFun :: Ty -> Ty -> Ty
  -- | forall a. t
  TForall :: TName -> Ty -> Ty
  -- | <ts>
  TTuple :: [Ty] -> Ty


deriving stock instance Show Ty


instance Eq Ty where
  TVar a == TVar b = a == b
  TInt == TInt = True
  (s1 `TFun` s2) == (t1 `TFun` t2) = s1 == t1 && s2 == t2
  (TForall a s) == (TForall b t) = s == tsubst b (TVar a) t
  TTuple ss == TTuple ts = ss == ts
  _ == _ = False


class SubTys a where
  subTys :: Traversal' a Ty


instance SubTys Ty where
  subTys f = \case
    TVar a -> pure $ TVar a
    TInt -> pure TInt
    t1 `TFun` t2 -> TFun <$> f t1 <*> f t2
    TForall a t -> TForall a <$> f t
    TTuple ts -> TTuple <$> traverse f ts


instance PP.Pretty Ty where
  pretty = \case
    TVar x -> pp x
    TInt -> "int"
    t1 `TFun` t2 -> pp t1 <+> "->" <+> pp t2
    TForall a t -> "forall" <+> pp a <> "." <+> pp t
    TTuple ts -> angles $ fmap pp ts


ftv :: Ty -> S.Set TName
ftv = \case
  TVar a -> S.singleton a
  TInt -> mempty
  t1 `TFun` t2 -> ftv t1 <> ftv t2
  TForall a t -> S.delete a (ftv t)
  TTuple ts -> foldMap ftv ts


tsubst :: TName -> Ty -> Ty -> Ty
tsubst a t' = \case
  TVar b
    | a == b -> t'
    | otherwise -> TVar b
  TInt -> TInt
  t1 `TFun` t2 -> tsubst a t' t1 `TFun` tsubst a t' t2
  TForall b t
    | a == b -> TForall b t
    | otherwise -> TForall b (tsubst a t' t)
  TTuple ts -> TTuple $ fmap (tsubst a t') ts


-- | u
data Tm where
  -- | x : t
  Var :: Name -> Maybe Ty -> Tm
  -- | i
  IntLit :: Int -> Tm
  -- | letrec x1 : t = e1 and ... in e end
  LetRec :: M.Map Name Tm -> Tm -> Tm
  -- | \x1 : t. e
  Abs :: Name -> Maybe Ty -> Tm -> Tm
  -- | e1 e2
  App :: Tm -> Tm -> Tm
  -- | prod a. e
  AbsT :: TName -> Tm -> Tm
  -- | e[t]
  AppT :: Tm -> Ty -> Tm
  -- | <es>
  Tuple :: [Tm] -> Tm
  -- | at i e
  At :: Int -> Tm -> Tm
  -- | e1 p e2
  Arith :: Prim -> Tm -> Tm -> Tm
  -- | if0(e1, e2, e3)
  If0 :: Tm -> Tm -> Tm -> Tm
  -- | e: t
  Ann :: Tm -> Ty -> Tm


deriving stock instance Eq Tm


deriving stock instance Show Tm


instance SubTys Tm where
  subTys f = \case
    Var x t -> Var x <$> traverse f t
    IntLit i -> pure $ IntLit i
    LetRec xs e -> LetRec <$> traverse (subTys f) xs <*> subTys f e
    Abs x t e -> Abs x <$> traverse f t <*> subTys f e
    e1 `App` e2 -> App <$> subTys f e1 <*> subTys f e2
    AbsT a e -> AbsT a <$> subTys f e
    e `AppT` t -> AppT <$> subTys f e <*> f t
    Tuple es -> Tuple <$> traverse (subTys f) es
    At i e -> At i <$> subTys f e
    Arith p e1 e2 -> Arith p <$> subTys f e1 <*> subTys f e2
    If0 e1 e2 e3 -> If0 <$> subTys f e1 <*> subTys f e2 <*> subTys f e3
    e `Ann` t -> Ann <$> subTys f e <*> f t


tyOf :: Tm -> Ty
tyOf = \case
  Var _ (Just t) -> t
  Var _ Nothing -> error "Unannotated variable"
  IntLit _ -> TInt
  LetRec _xs e -> tyOf e
  Abs _x (Just t) e -> t `TFun` tyOf e
  Abs _ Nothing _ -> error "Abs: Unannotated argument"
  e1 `App` _
    | _ `TFun` t2 <- tyOf e1 -> t2
    | otherwise -> error "App: e1 is not a function"
  AbsT a e -> TForall a $ tyOf e
  e `AppT` t
    | TForall a t' <- tyOf e -> tsubst a t t'
    | otherwise -> error $ "AppT: Type of e is not TForall" <> show e
  Tuple es -> TTuple $ fmap tyOf es
  At i es
    | TTuple ts <- tyOf es ->
        if
          | Just t <- ts ^? ix (i - 1) -> t
          | otherwise -> error "At: Index out of range"
    | otherwise -> error "At: Type of es is not TTuple"
  Arith{} -> TInt
  If0 _ e _ -> tyOf e
  _ `Ann` t -> t


ppSimp :: Tm -> PP.Doc ann
ppSimp e = case e of
  -- Var{} -> pp e
  IntLit{} -> pp e
  Tuple{} -> pp e
  _ -> parens [pp e]


instance PP.Pretty Tm where
  pretty = \case
    Var x (Just t) -> pp x <+> ":" <+> pp t
    Var x Nothing -> pp x
    IntLit i -> pp i
    LetRec xs e ->
      PP.vsep
        [ nest $
            PP.vsep $
              "let" : fmap (\(x, v) -> pp x <+> "=" <+> pp v <> ";") (M.toList xs)
        , nest $ PP.vsep ["in", pp e]
        ]
    Abs x t e -> "\\" <> arg <> "." <+> pp e
      where
        arg = case t of
          Just t' -> pp x <+> ":" <+> pp t'
          Nothing -> pp x
    e1 `App` e2 -> ppSimp e1 <+> ppSimp e2
    AbsT a e -> "prod" <+> pp a <> "." <+> pp e
    e `AppT` t -> ppSimp e <+> "@" <> pp t
    Tuple ts -> angles $ fmap pp ts
    At i e -> "at" <+> pp i <+> ppSimp e
    Arith p e1 e2 -> ppSimp e1 <+> pp p <+> ppSimp e2
    If0 e1 e2 e3 -> "if0" <> parens [pp e1, pp e2, pp e3]
    e `Ann` t -> pp e <+> ":" <+> pp t


-- | p
data Prim
  = -- | +
    Add
  | -- | -
    Sub
  | -- | *
    Mul


deriving stock instance Eq Prim


deriving stock instance Show Prim


instance PP.Pretty Prim where
  pretty = \case
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
