{-# LANGUAGE FieldSelectors #-}

module SF2TAL.Middle.Middle
  ( module SF2TAL.Name
  , TName
  , Name
  , KName
  , Ty (..)
  , Val (..)
  , Data (..)
  , BinOps (..)
  , Decl (..)
  , Tm (..)
  , TopLevel (..)
  , Plate (..)
  , TyOf (..)
  , fv
  , ftv
  , tExists
  , appT
  , tsubst
  )
where

import Data.Map qualified as M
import Data.Set qualified as S
import Prettyprinter qualified as PP
import SF2TAL.F (BinOps (..), Name, TName)
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Plate
import SF2TAL.Prelude
import Text.Megaparsec (SourcePos)


data K_


type KName = Name_ K_


-- | t
data Ty where
  -- | a
  TVar :: TName -> Ty
  -- | int
  TInt :: Ty
  -- | forall[as]. (ts){t} -> void
  TFix :: [TName] -> [Ty] -> Ty -> Ty
  -- | <ts>
  TTuple :: [Ty] -> Ty
  -- | exists a. t
  TExists :: TName -> Ty -> Ty


-- | v
data Val where
  -- | x : t
  Var :: Name -> Ty -> Val
  -- | i
  IntLit :: Int -> Val
  -- | v[t]
  AppT :: Val -> Ty -> Val
  -- | pack [t1, v] as t2
  Pack :: Ty -> Val -> Ty -> Val


data Data where
  -- | \[as](x1: t1, ..., xn: tn){k: t}. e
  Abs :: [TName] -> [(Name, Ty)] -> KName -> Ty -> Tm -> Data
  -- | <vs>
  Tuple :: [Val] -> Data


-- | d
data Decl where
  -- | v
  Bind :: Name -> Val -> Decl
  -- | rec ds
  Rec :: M.Map Name Data -> Decl
  -- | k = \(x: t) e
  BindK :: KName -> Name -> Ty -> Tm -> Decl
  -- | x = at i v (One-based index)
  At :: Name -> Int -> Val -> Decl
  -- | x = v1 p v2
  BinOp :: Name -> BinOps -> Val -> Val -> Decl
  -- | [a, x] = unpack v
  Unpack :: TName -> Name -> Val -> Decl


data Tm where
  -- | K, C, H, A: let d in e
  Let :: Decl -> Tm -> Tm
  -- | K, C, H, A: k v
  AppK :: KName -> Val -> Tm
  -- | K, C, H, A: v[ts](vs){k}
  App :: Val -> [Ty] -> [Val] -> KName -> Tm
  -- | K, C, H, A: if(v, k1, k2)
  If :: Val -> KName -> KName -> Tm
  Loc :: SourcePos -> Tm -> Tm


newtype TopLevel = TopLevel (M.Map Name Data)


deriving stock instance Show Ty


deriving stock instance Show Val


deriving stock instance Show Data


deriving stock instance Show Decl


deriving stock instance Show Tm


deriving stock instance Show TopLevel


instance Eq Ty where
  TVar x == TVar y = x == y
  TInt == TInt = True
  TFix (a : as) ss s == TFix (b : bs) ts t =
    TFix as ss s == tsubst b (TVar a) (TFix bs ts t)
  TFix [] ss s == TFix [] ts t = ss == ts && s == t
  TTuple ss == TTuple ts = ss == ts
  TExists a s == TExists b t = s == tsubst b (TVar a) t
  _ == _ = False


data Plate f = Plate
  { pTy :: Ty -> f Ty
  , pVal :: Val -> f Val
  , pData :: Data -> f Data
  , pTm :: Tm -> f Tm
  }


instance Multiplate Plate where
  multiplate (p :: Plate f) = Plate{pTy, pVal, pData, pTm}
    where
      infixl 4 <$>:
      infixl 4 <*>:
      (<$>:) :: ProjOf Plate a => (a -> b) -> a -> f b
      f <$>: x = f <$> getProj p x
      (<*>:) :: ProjOf Plate a => f (a -> b) -> a -> f b
      f <*>: x = f <*> getProj p x

      pTy = \case
        TVar x -> pure $ TVar x
        TInt -> pure TInt
        TFix as ts t -> TFix as <$> traverse (getProj p) ts <*>: t
        TTuple ts -> TTuple <$> traverse (getProj p) ts
        TExists a t -> TExists a <$>: t

      pVal = \case
        Var x t -> Var x <$>: t
        IntLit i -> pure $ IntLit i
        v `AppT` t -> AppT <$>: v <*>: t
        Pack t1 v t2 -> Pack <$>: t1 <*>: v <*>: t2

      pData = \case
        Abs as xs k kt e ->
          Abs as <$> traverseOf (each . _2) (getProj p) xs <*> pure k <*>: kt <*>: e
        Tuple vs -> Tuple <$> traverse (getProj p) vs

      pTm = \case
        Let (Bind x v) e -> Let <$> (Bind x <$>: v) <*>: e
        Let (Rec xs) e -> Let <$> (Rec <$> traverse (getProj p) xs) <*>: e
        Let (BindK x x1 t1 e1) e -> Let <$> (BindK x x1 <$>: t1 <*>: e1) <*>: e
        Let (At x i y) e -> Let (At x i y) <$>: e
        Let (BinOp x op y1 y2) e -> Let (BinOp x op y1 y2) <$>: e
        Let (Unpack a x v) e -> Let <$> (Unpack a x <$>: v) <*>: e
        AppK x y -> pure $ AppK x y
        App x ts xs k ->
          App x <$> traverse (getProj p) ts <*> pure xs <*> pure k
        If x e1 e2 -> pure $ If x e1 e2
        Loc l e -> Loc l <$>: e


  mkPlate f = Plate (f pTy) (f pVal) (f pData) (f pTm)


instance ProjOf Plate Ty where
  getProj = pTy


instance ProjOf Plate Val where
  getProj = pVal


instance ProjOf Plate Data where
  getProj = pData


instance ProjOf Plate Tm where
  getProj = pTm


-- | exists[as]. t
tExists :: [TName] -> Ty -> Ty
tExists as t = foldr TExists t as


-- | v[ts]
appT :: Val -> [Ty] -> Val
appT = foldl AppT


class TyOf a where
  tyOf :: a -> Ty


instance TyOf Val where
  tyOf = \case
    Var _ t -> t
    IntLit _ -> TInt
    v `AppT` t ->
      if
        | TFix (a : as) ts tk <- tyOf v -> TFix as (tsubst a t <$> ts) tk
        | otherwise -> error "ty: App: v is not TFix"
    Pack _t1 _v t2 -> t2


instance TyOf Data where
  tyOf (Abs as xs _k kt _e) = TFix as (xs ^.. each . _2) kt
  tyOf (Tuple vs) = TTuple $ fmap tyOf vs


ftv :: ProjOf Plate a => a -> S.Set TName
ftv = foldFor plate
  where
    plate = purePlate{pTy, pData}
    pTy = \case
      TVar a -> Const $ S.singleton a
      TFix as ts t -> Const $ foldMap ftv (t : ts) `S.difference` S.fromList as
      TExists x t -> Const $ S.delete x (ftv t)
      t -> traverseMFor (multiplate plate) t
    pData = \case
      Abs as xs _k _kt e ->
        Const $ (foldMap (ftv . snd) xs <> ftv e) `S.difference` S.fromList as
      Tuple vs -> Const $ foldMap ftv vs


fv :: ProjOf Plate a => a -> M.Map Name Ty
fv = foldFor plate
  where
    plate = purePlate{pVal, pData, pTm}
    pVal = \case
      Var x t -> Const $ M.singleton x t
      v -> traverseMFor (multiplate plate) v

    pData = \case
      Abs _as xs _k _kt e ->
        Const $ foldr ((\y -> at y .~ Nothing) . (^. _1)) (fv e) xs
      Tuple vs -> Const $ foldMap fv vs

    pTm = \case
      Let (Bind x v) e -> Const $ fv v <> (fv e & at x .~ Nothing)
      Let (Rec xs) e -> Const $ (foldMap fv xs <> fv e) M.\\ xs
      Let (BindK _k x _t e1) e -> Const $ (fv e1 & at x .~ Nothing) <> fv e
      Let (At x _i v) e -> Const $ fv v <> (fv e & at x .~ Nothing)
      Let (BinOp x _p v1 v2) e -> Const $ fv v1 <> fv v2 <> (fv e & at x .~ Nothing)
      Let (Unpack _a x v) e -> Const $ fv v <> (fv e & at x .~ Nothing)
      e -> traverseMFor (multiplate plate) e


tsubst :: ProjOf Plate a => TName -> Ty -> a -> a
tsubst a t' = traverseFor $ preMap $ purePlate{pTy}
  where
    pTy = \case
      TVar b | a == b -> pure t'
      t -> pure t


instance PP.Pretty Ty where
  pretty = \case
    TVar x -> pp x
    TInt -> "int"
    TFix as xs t
      | null as -> body
      | otherwise -> nest $ PP.sep [quantifier, body]
      where
        quantifier = "forall" <> brackets (fmap pp as) <> "."
        body = parens (fmap pp xs) <> braces [pp t] <+> "-> void"
    TTuple ts -> angles $ fmap pp ts
    TExists a t -> nest $ PP.sep ["exists" <+> pp a <> PP.dot, pp t]


instance PP.Pretty Val where
  pretty = \case
    Var x t -> pp x -- <+> ":" <+> pp t
    IntLit i -> pp i
    v `AppT` t -> parens [pp v] <> brackets [pp t]
    Pack t1 v t2 ->
      nest $ PP.sep ["pack" <+> brackets [pp t1, pp v] <+> "as", pp t2]


instance PP.Pretty Data where
  pretty = \case
    Abs as xs k kt e ->
      PP.group $
        "\\"
          <> (if null as then mempty else brackets (fmap pp as))
          <> parens (fmap (\(x, v) -> pp x <+> ":" <+> pp v) xs)
          <> braces [pp k <+> ":" <+> pp kt]
          <> "."
          <> nest (PP.line <> pp e)
    Tuple vs -> angles (fmap pp vs)


ppDecl :: PP.Doc a -> PP.Doc a -> PP.Doc a
ppDecl x v = nest $ PP.vsep [x <+> PP.equals, v]


instance PP.Pretty Decl where
  pretty = \case
    Bind x v -> ppDecl (pp x) (pp v)
    Rec xs ->
      "rec" <+> foldMap (\(x, v) -> ppDecl (pp x) (pp v)) (M.toList xs)
    BindK x k t e -> ppDecl (pp x) ("\\" <> pp k <+> ":" <+> pp t <> "." <+> pp e)
    At x i v -> ppDecl (pp x) ("at" <+> pp i <+> pp v)
    BinOp x p' v1 v2 ->
      ppDecl (pp x) (PP.sep [parens [pp v1], pp p' <+> parens [pp v2]])
    Unpack a x v ->
      ppDecl (brackets [pp a, pp x]) ("unpack" <+> parens [pp v])


instance PP.Pretty Tm where
  pretty = \case
    Let e1 e2 -> PP.vsep ["let" <+> pp e1 <+> "in", pp e2]
    AppK k x -> pp k <+> pp x
    App e1 ts xs k ->
      parens [pp e1]
        <> do if null ts then mempty else brackets (fmap pp ts)
        <> parens (fmap pp xs)
        <> braces [pp k]
    If v e1 e2 -> "if" <> parens [pp v, pp e1, pp e2]
    Loc l e -> pp e -- <+> fromString (sourcePosPretty l)]


instance PP.Pretty TopLevel where
  pretty (TopLevel datas) =
    PP.vsep $ fmap (\(x, d) -> ppDecl (pp x) (pp d)) (M.toList datas)
