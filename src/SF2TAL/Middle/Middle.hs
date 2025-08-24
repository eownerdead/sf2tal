{-# LANGUAGE FieldSelectors #-}

module SF2TAL.Middle.Middle
  ( TName
  , Name
  , KName
  , Ty (..)
  , Val (..)
  , Abs (..)
  , Prim (..)
  , Decl (..)
  , Tm (..)
  , Plate (..)
  , TyOf (..)
  , fv
  , ftv
  , tExists
  , appT
  , tsubst
  , subst
  )
where

import Data.Functor.Const
import Data.Map qualified as M
import Data.Set qualified as S
import Data.String
import Effectful
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import SF2TAL.F (Name, Prim (..))
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Plate
import SF2TAL.Uniq
import Text.Megaparsec (SourcePos, sourcePosPretty)


type TName = Int


data K_


type KName = Name_ K_


-- | t
data Ty where
  -- | K, C, H, A: a
  TVar :: TName -> Ty
  -- | K, C, H, A: int
  TInt :: Ty
  -- | K, C, H, A: forall[as]. (ts){t} -> void
  TFix :: [TName] -> [Ty] -> Ty -> Ty
  -- | K, C, H, A: <ts>
  TTuple :: [Ty] -> Ty
  -- | C, H, A: exists a. t
  TExists :: TName -> Ty -> Ty


-- | v
data Val where
  -- | K, C, H, A: x : t
  Var :: Name -> Ty -> Val
  -- | K, C, H, A: i
  IntLit :: Int -> Val
  -- | C, H, A: v[t]
  AppT :: Val -> Ty -> Val
  -- | C, H, A: pack [t1, v] as t2
  Pack :: Ty -> Val -> Ty -> Val


data Abs where
  -- | K, C, H, A: \[as](x1: t1, ..., xn: tn){k: t}. e
  Abs :: [TName] -> [(Name, Ty)] -> KName -> Ty -> Tm -> Abs


-- | d
data Decl where
  -- | K, C, H, A: x = v
  Bind :: Name -> Val -> Decl
  -- | K, C, H, A: k = \(x: t) e
  BindK :: KName -> Name -> Ty -> Tm -> Decl
  -- | K, C, H, A: rec ds
  Rec :: M.Map Name Abs -> Decl
  -- | K, C, H, A: x = at i v (One-based index)
  At :: Name -> Int -> Val -> Decl
  -- | K, C, H, A: x = v1 p v2
  Arith :: Name -> Prim -> Val -> Val -> Decl
  -- | C, H, A: [a, x] = unpack v
  Unpack :: TName -> Name -> Val -> Decl
  -- | A: x = <vs>
  CTuple :: Name -> [Val] -> Decl


data Tm where
  -- | K, C, H, A: let d in e
  Let :: Decl -> Tm -> Tm
  -- | K, C, H, A: k v
  AppK :: KName -> Val -> Tm
  -- | K, C, H, A: v[ts](vs){k}
  App :: Val -> [Ty] -> [Val] -> KName -> Tm
  -- | K, C, H, A: if0(v, k1, k2)
  If0 :: Val -> KName -> KName -> Tm
  -- | K, C, H, A: halt v
  Halt :: Val -> Tm
  Loc :: SourcePos -> Tm -> Tm


deriving stock instance Show Ty


deriving stock instance Show Val


deriving stock instance Show Abs


deriving stock instance Show Decl


deriving stock instance Show Tm


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
  , pAbs :: Abs -> f Abs
  , pTm :: Tm -> f Tm
  }


instance Multiplate Plate where
  multiplate (p :: Plate f) = Plate{pTy, pVal, pAbs, pTm}
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

      pAbs (Abs as xs k kt e) =
        Abs as <$> traverseOf (each . _2) (getProj p) xs <*> pure k <*>: kt <*>: e

      pTm = \case
        Let (Bind x v) e -> Let <$> (Bind x <$>: v) <*>: e
        Let (BindK x x1 t1 e1) e -> Let <$> (BindK x x1 <$>: t1 <*>: e1) <*>: e
        Let (Rec xs) e -> Let <$> (Rec <$> traverse (getProj p) xs) <*>: e
        Let (At x i y) e -> Let (At x i y) <$>: e
        Let (Arith x op y1 y2) e -> Let (Arith x op y1 y2) <$>: e
        Let (Unpack a x v) e -> Let <$> (Unpack a x <$>: v) <*>: e
        Let (CTuple x vs) e -> Let <$> (CTuple x <$> traverse (getProj p) vs) <*>: e
        AppK x y -> pure $ AppK x y
        App x ts xs k ->
          App x <$> traverse (getProj p) ts <*> pure xs <*> pure k
        If0 x e1 e2 -> pure $ If0 x e1 e2
        Halt x -> pure $ Halt x
        Loc l e -> Loc l <$>: e


  mkPlate f = Plate (f pTy) (f pVal) (f pAbs) (f pTm)


instance ProjOf Plate Ty where
  getProj = pTy


instance ProjOf Plate Val where
  getProj = pVal


instance ProjOf Plate Abs where
  getProj = pAbs


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


instance TyOf Abs where
  tyOf (Abs as xs _k kt _e) = TFix as (xs ^.. each . _2) kt


ftv :: ProjOf Plate a => a -> S.Set TName
ftv = foldFor plate
  where
    plate = purePlate{pTy, pAbs}
    pTy = \case
      TVar a -> Const $ S.singleton a
      TFix as ts t -> Const $ foldMap ftv (t : ts) `S.difference` S.fromList as
      TExists x t -> Const $ S.delete x (ftv t)
      t -> traverseMFor (multiplate plate) t
    pAbs = \case
      Abs as xs _k _kt e ->
        Const $ (foldMap (ftv . snd) xs <> ftv e) `S.difference` S.fromList as


fv :: ProjOf Plate a => a -> M.Map Name Ty
fv = foldFor plate
  where
    plate = purePlate{pAbs, pVal, pTm}
    pAbs = \case
      Abs _as xs _k _kt e ->
        Const $ foldr ((\y -> at y .~ Nothing) . (^. _1)) (fv e) xs

    pVal = \case
      Var x t -> Const $ M.singleton x t
      v -> traverseMFor (multiplate plate) v

    pTm = \case
      Let (Bind x v) e -> Const $ fv v <> (fv e & at x .~ Nothing)
      Let (BindK _k x _t e1) e -> Const $ (fv e1 & at x .~ Nothing) <> fv e
      Let (At x _i v) e -> Const $ fv v <> (fv e & at x .~ Nothing)
      Let (Arith x _p v1 v2) e -> Const $ fv v1 <> fv v2 <> (fv e & at x .~ Nothing)
      Let (Rec xs) e -> Const $ (foldMap fv xs <> fv e) M.\\ xs
      e -> traverseMFor (multiplate plate) e


tsubst :: ProjOf Plate a => TName -> Ty -> a -> a
tsubst a t' = traverseFor $ preMap $ purePlate{pTy}
  where
    pTy = \case
      TVar b | a == b -> pure t'
      t -> pure t


subst :: (Uniq :> es, ProjOf Plate a) => M.Map Name Val -> a -> Eff es a
subst sub = traverseMFor plate
  where
    plate = purePlate{pAbs}
    pAbs = \case
      Abs as xs k kt e -> do
        xs' <- traverse (const freshName) xs
        let xs'' = zip xs' (fmap snd xs)
        let sub' = M.fromList $ zip (fmap fst xs) $ fmap (uncurry Var) xs''
        Abs as xs'' k kt <$> subst (sub <> sub') e


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
    Var x t -> pp x <+> ":" <+> pp t
    IntLit i -> pp i
    v `AppT` t -> parens [pp v] <> brackets [pp t]
    Pack t1 v t2 ->
      nest $ PP.sep ["pack" <+> brackets [pp t1, pp v] <+> "as", pp t2]


instance PP.Pretty Abs where
  pretty (Abs as xs k kt e) =
    PP.group $
      "\\"
        <> (if null as then mempty else brackets (fmap pp as))
        <> parens (fmap (\(x, v) -> pp x <+> ":" <+> pp v) xs)
        <> braces [pp k <+> ":" <+> pp kt]
        <> "."
        <> nest (PP.line <> pp e)


ppDecl :: PP.Doc a -> PP.Doc a -> PP.Doc a
ppDecl x v = nest $ PP.sep [x <+> PP.equals, v]


instance PP.Pretty Decl where
  pretty = \case
    Bind x v -> ppDecl (pp x) (pp v)
    BindK x k t e -> ppDecl (pp x) ("\\" <> pp k <+> ":" <+> pp t <> "." <+> pp e)
    Rec xs ->
      "rec" <+> foldMap (\(x, v) -> ppDecl (pp x) (pp v)) (M.toList xs)
    At x i v -> ppDecl (pp x) ("at" <+> pp i <+> pp v)
    Arith x p' v1 v2 ->
      ppDecl (pp x) (PP.sep [parens [pp v1], pp p' <+> parens [pp v2]])
    Unpack a x v ->
      ppDecl (brackets [pp a, pp x]) ("unpack" <+> parens [pp v])
    CTuple x ts ->
      ppDecl (pp x) (angles (fmap pp ts))


instance PP.Pretty Tm where
  pretty = \case
    Let e1 e2 -> PP.vsep ["let" <+> pp e1 <+> "in", pp e2]
    AppK k x -> pp k <+> pp x
    App e1 ts xs k ->
      parens [pp e1]
        <> do if null ts then mempty else brackets (fmap pp ts)
        <> parens (fmap pp xs)
        <> braces [pp k]
    If0 v e1 e2 -> "if0" <> parens [pp v, pp e1, pp e2]
    Halt v -> nest $ PP.sep ["halt", parens [pp v]]
    Loc l e -> parens [pp e <+> fromString (sourcePosPretty l)]
