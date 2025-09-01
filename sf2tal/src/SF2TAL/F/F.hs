{-# LANGUAGE FieldSelectors #-}

module SF2TAL.F.F
  ( module SF2TAL.Name
  , TName
  , Name
  , Ty (..)
  , DeclsT
  , DeclsV
  , Decls (..)
  , BinOps (..)
  , Tm (..)
  , Plate (..)
  , tyOf
  , ftv
  , tsubst
  )
where

import Data.Map qualified as M
import Data.Set qualified as S
import Prettyprinter qualified as PP
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Plate
import SF2TAL.Prelude
import Text.Megaparsec (SourcePos, sourcePosPretty)


data T_


type TName = Name_ T_


data U_


type Name = Name_ U_


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


type DeclsT = M.Map TName Ty


type DeclsV = M.Map Name Tm


data Decls = Decls DeclsT DeclsV


-- | p
data BinOps
  = -- | +
    BAdd
  | -- | -
    BSub
  | -- | *
    BMul
  | -- | ==
    BEq
  | -- | /=
    BNe
  | -- | <
    BLt
  | -- | <=
    BLe


-- | u
data Tm where
  -- | x : t
  Var :: Name -> Maybe Ty -> Tm
  -- | i
  IntLit :: Int -> Tm
  -- | letrec x1 : t = e1 and ... in e end
  LetRec :: Decls -> Tm -> Tm
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
  BinOp :: BinOps -> Tm -> Tm -> Tm
  -- | if(e1, e2, e3)
  If :: Tm -> Tm -> Tm -> Tm
  -- | e: t
  Ann :: Tm -> Ty -> Tm
  Loc :: SourcePos -> Tm -> Tm


deriving stock instance Show Ty


deriving stock instance Show Decls


deriving stock instance Show BinOps


deriving stock instance Show Tm


instance Eq Ty where
  TVar a == TVar b = a == b
  TInt == TInt = True
  (s1 `TFun` s2) == (t1 `TFun` t2) = s1 == t1 && s2 == t2
  (TForall a s) == (TForall b t) = s == tsubst b (TVar a) t
  TTuple ss == TTuple ts = ss == ts
  _ == _ = False


deriving stock instance Eq BinOps


deriving stock instance Eq Decls


deriving stock instance Eq Tm


data Plate f = Plate
  { pTy :: Ty -> f Ty
  , pDecls :: Decls -> f Decls
  , pTm :: Tm -> f Tm
  }


instance ProjOf Plate Ty where
  getProj = pTy


instance ProjOf Plate Decls where
  getProj = pDecls


instance ProjOf Plate Tm where
  getProj = pTm


instance Multiplate Plate where
  multiplate (p :: Plate f) = Plate{pTy, pDecls, pTm}
    where
      infixl 4 <$>:
      infixl 4 <*>:
      (<$>:) :: ProjOf Plate a => (a -> b) -> a -> f b
      f <$>: x = f <$> getProj p x
      (<*>:) :: ProjOf Plate a => f (a -> b) -> a -> f b
      f <*>: x = f <*> getProj p x
      pTy = \case
        TVar a -> pure $ TVar a
        TInt -> pure TInt
        t1 `TFun` t2 -> TFun <$>: t1 <*>: t2
        TForall a t -> TForall a <$>: t
        TTuple ts -> TTuple <$> traverse (getProj p) ts

      pDecls (Decls ts es) = Decls <$> traverse (getProj p) ts <*> traverse (getProj p) es

      pTm = \case
        Var x t -> Var x <$> traverse (getProj p) t
        IntLit i -> pure $ IntLit i
        LetRec ds e -> LetRec <$>: ds <*>: e
        Abs x t e -> Abs x <$> traverse (getProj p) t <*>: e
        e1 `App` e2 -> App <$>: e1 <*>: e2
        AbsT a e -> AbsT a <$>: e
        e `AppT` t -> AppT <$>: e <*>: t
        Tuple es -> Tuple <$> traverse (getProj p) es
        At i e -> At i <$>: e
        BinOp op e1 e2 -> BinOp op <$>: e1 <*>: e2
        If e1 e2 e3 -> If <$>: e1 <*>: e2 <*>: e3
        e `Ann` t -> Ann <$>: e <*>: t
        Loc l e -> Loc l <$>: e


  mkPlate f = Plate (f pTy) (f pDecls) (f pTm)


tyOf :: Tm -> Ty
tyOf = \case
  Var _ (Just t) -> t
  Var _ Nothing -> error "Unannotated variable"
  IntLit _ -> TInt
  LetRec _ds e -> tyOf e
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
  BinOp{} -> TInt
  If _ e _ -> tyOf e
  _ `Ann` t -> t
  Loc _ e -> tyOf e


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


ppSimp :: Tm -> PP.Doc ann
ppSimp e = case e of
  -- Var{} -> pp e
  IntLit{} -> pp e
  Tuple{} -> pp e
  _ -> parens [pp e]


instance PP.Pretty Ty where
  pretty = \case
    TVar x -> pp x
    TInt -> "int"
    t1 `TFun` t2 -> pp t1 <+> "->" <+> pp t2
    TForall a t -> "forall" <+> pp a <> "." <+> pp t
    TTuple ts -> angles $ fmap pp ts


instance PP.Pretty BinOps where
  pretty = \case
    BAdd -> "+"
    BSub -> "-"
    BMul -> "*"
    BEq -> "=="
    BNe -> "/="
    BLt -> "<"
    BLe -> "<="


instance PP.Pretty Decls where
  pretty (Decls ts es) =
    PP.vsep $
      fmap (\(x, v) -> "type" <+> pp x <+> "=" <+> pp v <> ";") (M.toList ts)
        <> fmap (\(x, v) -> pp x <+> "=" <+> pp v <> ";") (M.toList es)


instance PP.Pretty Tm where
  pretty = \case
    Var x (Just t) -> pp x <+> ":" <+> pp t
    Var x Nothing -> pp x
    IntLit i -> pp i
    LetRec ds e ->
      PP.vsep
        [ nest $ PP.vsep ["let", pp ds]
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
    BinOp p e1 e2 -> ppSimp e1 <+> pp p <+> ppSimp e2
    If e1 e2 e3 -> "if" <> parens [pp e1, pp e2, pp e3]
    e `Ann` t -> pp e <+> ":" <+> pp t
    Loc l e -> parens [pp e <+> fromString (sourcePosPretty l)]
