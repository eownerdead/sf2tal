{-# LANGUAGE FieldSelectors #-}

module SF2TAL.Middle.Middle
  ( TName
  , Ty (..)
  , Val (..)
  , Decl (..)
  , Tm (..)
  , Plate (..)
  , TyOf (..)
  , fv
  , ftv
  , tTupleInitN
  , tTuple
  , tTupleUninited
  , tTupleInitedToN
  , tExists
  , appT
  , tsubst
  , subst
  )
where

import Control.Exception (assert)
import Data.Functor.Const
import Data.Map qualified as M
import Data.Set qualified as S
import Data.String (fromString)
import Effectful
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import SF2TAL.F (Prim)
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Plate
import SF2TAL.Uniq
import Text.Megaparsec (SourcePos, sourcePosPretty)


type TName = Int


-- | t
data Ty where
  -- | K, C, H, A: a
  TVar :: TName -> Ty
  -- | K, C, H, A: int
  TInt :: Ty
  -- | K, C, H, A: forall[as]. (ts) -> void
  TFix :: [TName] -> [Ty] -> Ty
  -- | K, C, H, A: ^ <ts>
  TTuple :: [(Ty, Bool)] -> Ty
  -- | C, H, A: exists a. t
  TExists :: TName -> Ty -> Ty


-- | v
data Val where
  -- | K, C, H, A: x : t
  Var :: Name -> Ty -> Val
  -- | K, C, H, A: i
  IntLit :: Int -> Val
  -- | K, C, H, A: [as](x1: t1, ..., xn: tn). e
  Abs :: [TName] -> [(Name, Ty)] -> Tm -> Val
  -- | K, C, H, A: <vs>
  Tuple :: [Val] -> Val
  -- | C, H, A: v[t]
  AppT :: Val -> Ty -> Val
  -- | C, H, A: pack [t1, v] as t2
  Pack :: Ty -> Val -> Ty -> Val


-- | d
data Decl where
  -- | K, C, H, A: x = v
  Bind :: Name -> Val -> Decl
  -- | K, C, H, A: x = at i v (One-based index)
  At :: Name -> Int -> Val -> Decl
  -- | K, C, H, A: x = v1 p v2
  Arith :: Name -> Prim -> Val -> Val -> Decl
  -- | C, H, A: [a, x] = unpack v
  Unpack :: TName -> Name -> Val -> Decl
  -- | A: x = malloc ts
  Malloc :: Name -> [Ty] -> Decl
  -- | A: x = v1[i] <- v2
  Update :: Name -> Val -> Int -> Val -> Decl


data Tm where
  -- | K, C, H, A: let d in e
  Let :: Decl -> Tm -> Tm
  -- | K, C, H, A: letrec x1 = v1 and ... in e
  LetRec :: M.Map Name Val -> Tm -> Tm
  -- | K, C, H, A: v[ts](vs)
  App :: Val -> [Ty] -> [Val] -> Tm
  -- | K, C, H, A: if0(v, e1, e2)
  If0 :: Val -> Tm -> Tm -> Tm
  -- | K, C, H, A: halt v
  Halt :: Val -> Tm
  Loc :: SourcePos -> Tm -> Tm


deriving stock instance Show Ty


deriving stock instance Show Val


deriving stock instance Show Tm


deriving stock instance Show Decl


instance Eq Ty where
  TVar x == TVar y = x == y
  TInt == TInt = True
  TFix (a : as) ss == TFix (b : bs) ts =
    TFix as ss == tsubst b (TVar a) (TFix bs ts)
  TFix [] ss == TFix [] ts = ss == ts
  TTuple ss == TTuple ts = ss == ts
  TExists a s == TExists b t = s == tsubst b (TVar a) t
  _ == _ = False


data Plate f = Plate
  { pTy :: Ty -> f Ty
  , pVal :: Val -> f Val
  , pTm :: Tm -> f Tm
  }


instance Multiplate Plate where
  multiplate (p :: Plate f) = Plate{pTy, pVal, pTm}
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
        TFix as ts -> TFix as <$> traverse (getProj p) ts
        TTuple ts -> TTuple <$> traverseOf (each . _1) (getProj p) ts
        TExists a t -> TExists a <$>: t

      pVal = \case
        Var x t -> Var x <$>: t
        IntLit i -> pure $ IntLit i
        Abs as xs e -> Abs as <$> traverseOf (each . _2) (getProj p) xs <*>: e
        Tuple vs -> Tuple <$> traverse (getProj p) vs
        v `AppT` t -> AppT <$>: v <*>: t
        Pack t1 v t2 -> Pack <$>: t1 <*>: v <*>: t2

      pTm = \case
        Let (Bind x v) e -> Let <$> (Bind x <$>: v) <*>: e
        Let (At x i v) e -> Let <$> (At x i <$>: v) <*>: e
        Let (Arith x op v1 v2) e -> Let <$> (Arith x op <$>: v1 <*>: v2) <*>: e
        Let (Unpack a x v) e -> Let <$> (Unpack a x <$>: v) <*>: e
        Let (Malloc x ts) e -> Let <$> (Malloc x <$> traverse (getProj p) ts) <*>: e
        Let (Update x v1 i v2) e -> Let <$> (Update x <$>: v1 <*> pure i <*>: v2) <*>: e
        LetRec xs e -> LetRec <$> traverse (getProj p) xs <*>: e
        App v ts vs -> App <$>: v <*> traverse (getProj p) ts <*> traverse (getProj p) vs
        If0 v e1 e2 -> If0 <$>: v <*>: e1 <*>: e2
        Halt v -> Halt <$>: v
        Loc l e -> Loc l <$>: e


  mkPlate f = Plate (f pTy) (f pVal) (f pTm)


instance ProjOf Plate Ty where
  getProj = pTy


instance ProjOf Plate Val where
  getProj = pVal


instance ProjOf Plate Tm where
  getProj = pTm


tTupleInitN :: Int -> Ty -> Ty
tTupleInitN n = \case
  TTuple ts -> TTuple (ts & ix (n - 1) . _2 .~ True)
  _ -> error "tTupleInitN: not TTuple"


tTuple :: [Ty] -> Ty
tTuple = TTuple . fmap (,True)


tTupleUninited :: [Ty] -> Ty
tTupleUninited = TTuple . fmap (,False)


tTupleInitedToN :: Int -> [Ty] -> Ty
tTupleInitedToN i ts = foldr tTupleInitN (tTupleUninited ts) [1 .. i]


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
    Abs as xs _e -> TFix as (fmap (^. _2) xs)
    Tuple vs -> TTuple $ fmap ((,True) . tyOf) vs
    v `AppT` t ->
      if
        | TFix (a : as) ts <- tyOf v -> TFix as (tsubst a t <$> ts)
        | otherwise -> error "ty: App: v is not TFix"
    Pack _t1 _v t2 -> t2


ftv :: ProjOf Plate a => a -> S.Set TName
ftv = foldFor plate
  where
    plate = purePlate{pTy, pVal}
    pTy = \case
      TVar a -> Const $ S.singleton a
      TFix as ts -> Const $ foldMap ftv ts `S.difference` S.fromList as
      TExists x t -> Const $ S.delete x (ftv t)
      t -> traverseMFor (multiplate plate) t
    pVal = \case
      Abs as xs e ->
        Const $ (foldMap (ftv . snd) xs <> ftv e) `S.difference` S.fromList as
      v -> traverseMFor (multiplate plate) v


fv :: ProjOf Plate a => a -> M.Map Name Ty
fv = foldFor plate
  where
    plate = purePlate{pVal, pTm}
    pVal = \case
      Var x t -> Const $ M.singleton x t
      Abs _as xs e ->
        Const $ foldr ((\y -> at y .~ Nothing) . (^. _1)) (fv e) xs
      v -> traverseMFor (multiplate plate) v

    pTm = \case
      Let (Bind x v) e -> Const $ fv v <> (fv e & at x .~ Nothing)
      Let (At x _i v) e -> Const $ fv v <> (fv e & at x .~ Nothing)
      Let (Arith x _p v1 v2) e -> Const $ fv v1 <> fv v2 <> (fv e & at x .~ Nothing)
      Let _d _e -> error "No need"
      LetRec xs e -> Const $ (foldMap fv xs <> fv e) M.\\ xs
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
    plate = purePlate{pVal}
    pVal = \case
      Var x t
        | Just v' <- M.lookup x sub ->
            assert (t == tyOf v') do pure v'
        | otherwise -> pure $ Var x t
      Abs as xs e -> do
        xs' <- traverse (const freshName) xs
        let xs'' = zip xs' (fmap snd xs)
        let sub' = M.fromList $ zip (fmap fst xs) $ fmap (uncurry Var) xs''
        Abs as xs'' <$> subst (sub <> sub') e
      v -> traverseMFor (multiplate plate) v


instance PP.Pretty Ty where
  pretty = \case
    TVar x -> pp x
    TInt -> "int"
    TFix as xs
      | null as -> body
      | otherwise -> nest $ PP.sep [quantifier, body]
      where
        quantifier = "forall" <> brackets (fmap pp as) <> "."
        body = parens (fmap pp xs) <+> "-> void"
    TTuple ts ->
      angles $ fmap (\(t, i) -> (if i then mempty else "*") <> pp t) ts
    TExists a t -> nest $ PP.sep ["exists" <+> pp a <> PP.dot, pp t]


instance PP.Pretty Val where
  pretty = \case
    Var x t -> pp x <+> ":" <+> pp t
    IntLit i -> pp i
    Abs as xs e ->
      PP.group $
        "\\"
          <> (if null as then mempty else brackets (fmap pp as))
          <> parens (fmap (\(k, v) -> pp k <+> ":" <+> pp v) xs)
          <> "."
          <> nest (PP.line <> pp e)
    Tuple vs -> angles $ fmap pp vs
    v `AppT` t -> parens [pp v] <> brackets [pp t]
    Pack t1 v t2 ->
      nest $ PP.sep ["pack" <+> brackets [pp t1, pp v] <+> "as", pp t2]


ppDecl :: PP.Doc a -> PP.Doc a -> PP.Doc a
ppDecl x v = nest $ PP.sep [x <+> PP.equals, v]


instance PP.Pretty Decl where
  pretty = \case
    Bind x v -> ppDecl (pp x) (pp v)
    At x i v -> ppDecl (pp x) ("at" <+> pp i <+> pp v)
    Arith x p' v1 v2 ->
      ppDecl (pp x) (PP.sep [parens [pp v1], pp p' <+> parens [pp v2]])
    Unpack a x v ->
      ppDecl (brackets [pp a, pp x]) ("unpack" <+> parens [pp v])
    Malloc x ts ->
      ppDecl (pp x) ("malloc" <+> brackets (fmap pp ts))
    Update x v1 i v2 ->
      nest $
        PP.sep
          [ pp x <+> PP.equals
          , nest $ PP.sep [parens [pp v1] <> brackets [pp i] <+> "<-", pp v2]
          ]


instance PP.Pretty Tm where
  pretty = \case
    Let e1 e2 -> PP.vsep ["let" <+> pp e1 <+> "in", pp e2]
    LetRec xs e ->
      PP.vsep
        [ nest $ PP.vsep $ "letrec" : fmap (\(x, v) -> ppDecl (pp x) (pp v)) (M.toList xs)
        , nest $ PP.vsep ["in", pp e]
        ]
    App e1 ts xs ->
      parens [pp e1]
        <> do if null ts then mempty else brackets (fmap pp ts)
        <> parens (fmap pp xs)
    If0 v e1 e2 -> "if0" <> parens [pp v, pp e1, pp e2]
    Halt v -> nest $ PP.sep ["halt", parens [pp v]]
    Loc l e -> parens [pp e <+> fromString (sourcePosPretty l)]
