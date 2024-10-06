module SF2TAL.Middle.Middle
  ( TName
  , Name
  , Fv (..)
  , Ftv (..)
  , Ty (..)
  , SubTys (..)
  , subst
  , tTupleInitN
  , tTuple
  , tTupleUninited
  , tTupleInitedToN
  , tsubst
  , tExists
  , Val (..)
  , appT
  , Ann (..)
  , SubAnns (..)
  , HasVal (..)
  , HasTy (..)
  , Decl (..)
  , Tm (..)
  , Prog (..)
  )
where

import Data.Foldable
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Lens.Micro.Platform
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as PP
import SF2TAL.F (Prim)
import SF2TAL.Utils


type TName = Int


type Name = Int


class Fv a where
  fv :: a -> M.Map Name Ty


class Ftv a where
  ftv :: a -> S.Set TName


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


deriving stock instance Show Ty


instance Eq Ty where
  TVar x == TVar y = x == y
  TInt == TInt = True
  TFix (a : as) ss == TFix (b : bs) ts =
    TFix as ss == tsubst b (TVar a) (TFix bs ts)
  TFix [] ss == TFix [] ts = ss == ts
  TTuple ss == TTuple ts = ss == ts
  TExists a s == TExists b t = s == tsubst b (TVar a) t
  _ == _ = False


class SubTys a where
  subTys :: Traversal' a Ty


instance SubTys Ty where
  subTys f = \case
    TVar x -> pure $ TVar x
    TInt -> pure TInt
    TFix as ts -> TFix as <$> traverse f ts
    TTuple ts -> TTuple <$> traverseOf (each . _1) f ts
    TExists a t -> TExists a <$> f t


instance PP.Pretty Ty where
  pretty = \case
    TVar x -> pretty x
    TInt -> pretty ("int" :: T.Text)
    TFix as xs
      | null as -> body
      | otherwise -> PP.nest 2 $ PP.sep [quantifier, body]
      where
        quantifier =
          pretty ("forall" :: T.Text) <> brackets (fmap pretty as) <> PP.dot
        body = parens (fmap pretty xs) <+> pretty ("-> void" :: T.Text)
    TTuple ts ->
      angles $
        fmap
          ( \(t, i) ->
              (if i then mempty else pretty ("*" :: T.Text)) <> pretty t
          )
          ts
    TExists a t ->
      PP.nest 2 $
        PP.sep
          [ pretty ("exists" :: T.Text) <+> pretty a <> PP.dot
          , pretty t
          ]


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


tsubst :: TName -> Ty -> Ty -> Ty
tsubst a t' = transformOf subTys $ \case
  TVar b | a == b -> t'
  x -> x


instance Ftv Ty where
  ftv = \case
    TVar a -> S.singleton a
    TInt -> mempty
    TFix as ts -> foldMap ftv ts `S.difference` S.fromList as
    TTuple ts -> foldMap (ftv . fst) ts
    TExists x t -> S.delete x (ftv t)


-- | exists[as]. t
tExists :: [TName] -> Ty -> Ty
tExists as t = foldr TExists t as


-- | u
data Val where
  -- | K, C, H, A: x
  Var :: Name -> Val
  -- | K, C, H, A: i
  IntLit :: Int -> Val
  -- | K, C, H, A: fix x(x1: t1, ..., xn: tn). e
  Fix :: Maybe Name -> [TName] -> [(Name, Ty)] -> Tm -> Val
  -- | K, C, H, A: <vs>
  Tuple :: [Ann] -> Val
  -- | C, H, A: v[t]
  AppT :: Ann -> Ty -> Val
  -- | C, H, A: pack [t1, v] as t2
  Pack :: Ty -> Ann -> Ty -> Val


deriving stock instance Show Val


instance PP.Pretty Val where
  pretty = \case
    Var x -> pretty x
    IntLit i -> pretty i
    Fix x as xs e ->
      PP.group $
        ( case x of
            Just x' -> pretty ("fix " :: T.Text) <> pretty x'
            Nothing -> pretty ("fun" :: T.Text)
        )
          <> (if null as then mempty else brackets (fmap pretty as))
          <> parens (fmap (\(k, v) -> pretty k <+> PP.colon <+> pretty v) xs)
          <> PP.dot
          <> PP.nest 2 (PP.line <> pretty e)
    Tuple vs -> angles $ fmap pretty vs
    v `AppT` t -> parens [pretty v] <> brackets [pretty t]
    Pack t1 v t2 ->
      PP.nest 2 $
        PP.sep
          [ pretty ("pack" :: T.Text)
              <+> brackets [pretty t1, pretty v]
              <+> pretty ("as" :: T.Text)
          , pretty t2
          ]


-- | v
data Ann = Ann {val :: Val, ty :: Ty}


deriving stock instance Show Ann


instance SubTys Val where
  subTys f = \case
    Var x -> pure $ Var x
    IntLit i -> pure $ IntLit i
    Fix x as xs e -> Fix x as xs <$> subTys f e
    Tuple vs -> Tuple <$> traverse (subTys f) vs
    v `AppT` t -> AppT <$> subTys f v <*> f t
    Pack t1 v t2 -> Pack <$> f t1 <*> subTys f v <*> f t2


class SubAnns a where
  subAnns :: Traversal' a Ann


instance SubAnns Val where
  subAnns f = \case
    Var x -> pure $ Var x
    IntLit i -> pure $ IntLit i
    Fix x as xs e -> Fix x as xs <$> subAnns f e
    Tuple vs -> Tuple <$> traverse f vs
    v `AppT` t -> (`AppT` t) <$> f v
    Pack t1 v t2 -> Pack t1 <$> f v <*> pure t2


instance SubAnns Ann where
  subAnns f (u `Ann` t) = (`Ann` t) <$> subAnns f u


instance SubTys Ann where
  subTys f (u `Ann` t) = Ann <$> subTys f u <*> f t


instance PP.Pretty Ann where
  pretty (v `Ann` t) =
    PP.group $
      pretty v <> PP.nest 2 (PP.line <> pretty (":" :: T.Text) <+> pretty t)


-- pretty (v `Ann` _) = pretty v

instance Fv Ann where
  fv (u `Ann` t) = case u of
    Var x -> M.singleton x t
    IntLit _ -> mempty
    Fix x _as xs e ->
      foldr (\y -> at y .~ Nothing) (fv e) (toList x <> (xs <&> (^. _1)))
    Tuple es -> foldMap fv es
    e `AppT` _t' -> fv e
    Pack _a v _t2 -> fv v


instance Ftv Ann where
  ftv (u `Ann` _) = case u of
    Var _x -> mempty
    IntLit _i -> mempty
    Fix _x as xs e ->
      (foldMap (ftv . snd) xs <> ftv e) `S.difference` S.fromList as
    Tuple es -> foldMap ftv es
    e `AppT` t -> ftv e <> ftv t
    Pack t1 v t2 -> ftv t1 <> ftv v <> ftv t2


subst :: SubAnns a => Name -> Ann -> a -> a
subst x v' =
  subAnns %~ \(u `Ann` t) -> case u of
    Var y
      | x == y -> v'
      | otherwise -> Var y `Ann` t
    _ -> subst x v' $ u `Ann` t


data Tm where
  -- | K, C, H, A: let d in e
  Let :: Decl -> Tm -> Tm
  -- | K, C, H, A: v[ts](vs)
  App :: Ann -> [Ty] -> [Ann] -> Tm
  -- | K, C, H, A: if0(v, e1, e2)
  If0 :: Ann -> Tm -> Tm -> Tm
  -- | K, C, H, A: halt[t] v
  Halt :: Ty -> Ann -> Tm


deriving stock instance Show Tm


instance SubTys Tm where
  subTys f = \case
    Let d e -> Let <$> subTys f d <*> subTys f e
    App v ts vs -> App <$> subTys f v <*> traverse f ts <*> traverse (subTys f) vs
    If0 v e1 e2 -> If0 <$> subTys f v <*> subTys f e1 <*> subTys f e2
    Halt t v -> Halt <$> f t <*> subTys f v


instance SubAnns Tm where
  subAnns f = \case
    Let d e -> Let <$> subAnns f d <*> subAnns f e
    App v ts vs -> App <$> f v <*> pure ts <*> traverse f vs
    If0 v e1 e2 -> If0 <$> f v <*> subAnns f e1 <*> subAnns f e2
    Halt t v -> Halt t <$> f v


instance PP.Pretty Tm where
  pretty = \case
    Let e1 e2 ->
      PP.vsep
        [ pretty ("let" :: T.Text) <+> pretty e1 <+> pretty ("in" :: T.Text)
        , pretty e2
        ]
    App e1 ts xs ->
      parens [pretty e1]
        <> (if null ts then mempty else brackets (fmap pretty ts))
        <> parens (fmap pretty xs)
    If0 v e1 e2 ->
      pretty ("if0" :: T.Text)
        <> parens [pretty v, pretty e1, pretty e2]
    Halt t v ->
      PP.nest 2 $
        PP.sep
          [pretty ("halt" :: T.Text) <> brackets [pretty t], parens [pretty v]]


instance Fv Tm where
  fv = \case
    Let (Bind x v) e -> fv v <> fv e & at x .~ Nothing
    Let (At x _i v) e -> fv v <> fv e & at x .~ Nothing
    Let (Arith x _p v1 v2) e -> fv v1 <> fv v2 <> fv e & at x .~ Nothing
    Let _d _e -> error "No need"
    App v _ts vs -> fv v <> foldMap fv vs
    If0 v e1 e2 -> fv v <> fv e1 <> fv e2
    Halt _t v -> fv v


instance Ftv Tm where
  ftv e = S.fromList $ e ^.. subTys . folding ftv


-- | d
data Decl where
  -- | K, C, H, A: x = v
  Bind :: Name -> Ann -> Decl
  -- | K, C, H, A: x = at i v (One-based index)
  At :: Name -> Int -> Ann -> Decl
  -- | K, C, H, A: x = v1 p v2
  Arith :: Name -> Prim -> Ann -> Ann -> Decl
  -- | C, H, A: [a, x] = unpack v
  Unpack :: TName -> Name -> Ann -> Decl
  -- | A: x = malloc ts
  Malloc :: Name -> [Ty] -> Decl
  -- | A: x = v1[i] <- v2
  Update :: Name -> Ann -> Int -> Ann -> Decl


deriving stock instance Show Decl


instance SubTys Decl where
  subTys f = \case
    Bind x v -> Bind x <$> subTys f v
    At x i v -> At x i <$> subTys f v
    Arith x p v1 v2 -> Arith x p <$> subTys f v1 <*> subTys f v2
    Unpack a x v -> Unpack a x <$> subTys f v
    Malloc x ts -> Malloc x <$> traverse f ts
    Update x v1 i v2 -> Update x <$> subTys f v1 <*> pure i <*> subTys f v2


instance SubAnns Decl where
  subAnns f = \case
    Bind x v -> Bind x <$> f v
    At x i v -> At x i <$> f v
    Arith x p v1 v2 -> Arith x p <$> f v1 <*> f v2
    Unpack a x v -> Unpack a x <$> f v
    Malloc x ts -> pure $ Malloc x ts
    Update x v1 i v2 -> Update x <$> f v1 <*> pure i <*> f v2


instance PP.Pretty Decl where
  pretty = \case
    Bind x v -> prettyDecl (pretty x) (pretty v)
    At x i v ->
      prettyDecl
        (pretty x)
        (pretty ("at" :: T.Text) <+> pretty i <+> pretty v)
    Arith x p v1 v2 ->
      prettyDecl
        (pretty x)
        (PP.sep [parens [pretty v1], pretty p <+> parens [pretty v2]])
    Unpack a x v ->
      prettyDecl
        (brackets [pretty a, pretty x])
        (pretty ("unpack" :: T.Text) <+> parens [pretty v])
    Malloc x ts ->
      prettyDecl
        (pretty x)
        (pretty ("malloc" :: T.Text) <+> brackets (fmap pretty ts))
    Update x v1 i v2 ->
      PP.nest 2 $
        PP.sep
          [ pretty x <+> PP.equals
          , PP.nest 2 $
              PP.sep
                [ parens [pretty v1]
                    <> brackets [pretty i]
                    <+> pretty ("<-" :: T.Text)
                , pretty v2
                ]
          ]


prettyDecl :: PP.Doc a -> PP.Doc a -> PP.Doc a
prettyDecl x v = PP.nest 2 $ PP.sep [x <+> PP.equals, v]


instance Ftv Decl where
  ftv e = S.fromList $ e ^.. subTys . folding ftv


-- | H, A: p
data Prog where
  LetRec :: M.Map Name Ann -> Tm -> Prog


deriving stock instance Show Prog


instance PP.Pretty Prog where
  pretty (LetRec xs e) =
    PP.vsep
      [ PP.nest
          2
          ( PP.vsep $
              pretty ("letrec" :: T.Text)
                : fmap
                  (\(k, v) -> prettyDecl (pretty k) (pretty v))
                  (M.toList xs)
          )
      , PP.nest 2 (PP.vsep [pretty ("in" :: T.Text), pretty e])
      ]


-- Order matters!
makeFieldsId ''Ann


-- | v[ts]
appT :: Ann -> [Ty] -> Ann
appT v [] = (v ^. val) `Ann` (v ^. ty)
appT v@(_ `Ann` (TFix (a : as) ts')) (t : ts) =
  ((v `AppT` t) `Ann` TFix as (fmap (tsubst a t) ts')) `appT` ts
appT v ts = error $ "appT: " <> show (v, ts)
