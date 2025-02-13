module SF2TAL.Middle.Middle
  ( Fv (..)
  , Ftv (..)
  , Ty (..)
  , tTupleInitN
  , tTuple
  , tTupleUninited
  , tTupleInitedToN
  , tsubst
  , tExists
  , Val (..)
  , appT
  , Ann (..)
  , HasVal (..)
  , HasTy (..)
  , Decl (..)
  , Tm (..)
  , Prog (..)
  )
where

import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Text qualified as T
import Lens.Micro.Platform
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as PP
import SF2TAL.F (Prim)
import SF2TAL.Utils


class Fv a where
  fv :: a -> HM.HashMap Name Ty


class Ftv a where
  ftv :: a -> HS.HashSet TName


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


instance PP.Pretty Ty where
  pretty (TVar x) = pretty x
  pretty TInt = pretty ("int" :: T.Text)
  pretty (TFix as xs)
    | null as = body
    | otherwise = PP.nest 2 $ PP.sep [quantifier, body]
    where
      quantifier =
        pretty ("forall" :: T.Text) <> brackets (fmap pretty as) <> PP.dot
      body = parens (fmap pretty xs) <+> pretty ("-> void" :: T.Text)
  pretty (TTuple ts) =
    angles $
      fmap
        ( \(t, i) ->
            (if i then mempty else pretty ("*" :: T.Text)) <> pretty t
        )
        ts
  pretty (TExists a t) =
    PP.nest 2 $
      PP.sep
        [ pretty ("exists" :: T.Text) <+> pretty a <> PP.dot
        , pretty t
        ]


tTupleInitN :: Int -> Ty -> Ty
tTupleInitN n (TTuple ts) = TTuple (ts & ix (n - 1) . _2 .~ True)
tTupleInitN _ _ = error "tTupleInitN: not TTuple"


tTuple :: [Ty] -> Ty
tTuple = TTuple . fmap (,True)


tTupleUninited :: [Ty] -> Ty
tTupleUninited = TTuple . fmap (,False)


tTupleInitedToN :: Int -> [Ty] -> Ty
tTupleInitedToN i ts = foldr tTupleInitN (tTupleUninited ts) [1 .. i]


tsubst :: TName -> Ty -> Ty -> Ty
tsubst a t' (TVar b)
  | a == b = t'
  | otherwise = TVar b
tsubst _a _t' TInt = TInt
tsubst a t' (TFix as ts) = TFix as $ fmap (tsubst a t') ts
tsubst a t' (TTuple ts) = TTuple (ts <&> _1 %~ tsubst a t')
tsubst a t' (TExists b t) = TExists b $ tsubst a t' t


instance Ftv Ty where
  ftv (TVar a) = HS.singleton a
  ftv TInt = mempty
  ftv (TFix as ts) = foldMap ftv ts `HS.difference` HS.fromList as
  ftv (TTuple ts) = foldMap (ftv . fst) ts
  ftv (TExists x t) = HS.delete x (ftv t)


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
  Fix :: Name -> [TName] -> [(Name, Ty)] -> Tm -> Val
  -- | K, C, H, A: <vs>
  Tuple :: [Ann] -> Val
  -- | C, H, A: v[t]
  AppT :: Ann -> Ty -> Val
  -- | C, H, A: pack [t1, v] as t2
  Pack :: Ty -> Ann -> Ty -> Val


deriving stock instance Show Val


instance PP.Pretty Val where
  pretty (Var x) = pretty x
  pretty (IntLit i) = pretty i
  pretty (Fix x as xs e) =
    PP.group $
      ( if T.null x
          then pretty ("fun" :: T.Text)
          else pretty ("fix " :: T.Text) <> pretty x
      )
        <> (if null as then mempty else brackets (fmap pretty as))
        <> parens (fmap (\(k, v) -> pretty k <+> PP.colon <+> pretty v) xs)
        <> PP.dot
        <> PP.nest 2 (PP.line <> pretty e)
  pretty (Tuple vs) = angles $ fmap pretty vs
  pretty (v `AppT` t) = parens [pretty v] <> brackets [pretty t]
  pretty (Pack t1 v t2) =
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


instance PP.Pretty Ann where
  pretty (v `Ann` t) =
    PP.group $
      pretty v <> PP.nest 2 (PP.line <> pretty (":" :: T.Text) <+> pretty t)


-- pretty (v `Ann` _) = pretty v

instance Fv Ann where
  fv (u `Ann` t) = case u of
    Var x -> HM.singleton x t
    IntLit _ -> mempty
    Fix x _as xs e ->
      HM.filterWithKey (\k _ -> k `notElem` (x : fmap fst xs)) $ fv e
    Tuple es -> foldMap fv es
    e `AppT` _t' -> fv e
    Pack _a v _t2 -> fv v


instance Ftv Ann where
  ftv (u `Ann` _) = case u of
    Var _x -> mempty
    IntLit _i -> mempty
    Fix _x as xs e ->
      (foldMap (ftv . snd) xs <> ftv e) `HS.difference` HS.fromList as
    Tuple es -> foldMap ftv es
    e `AppT` t -> ftv e <> ftv t
    Pack t1 v t2 -> ftv t1 <> ftv v <> ftv t2


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


instance PP.Pretty Tm where
  pretty (Let e1 e2) =
    PP.vsep
      [ pretty ("let" :: T.Text) <+> pretty e1 <+> pretty ("in" :: T.Text)
      , pretty e2
      ]
  pretty (App e1 ts xs) =
    parens [pretty e1]
      <> (if null ts then mempty else brackets (fmap pretty ts))
      <> parens (fmap pretty xs)
  pretty (If0 v e1 e2) =
    pretty ("if0" :: T.Text)
      <> parens [pretty v, pretty e1, pretty e2]
  pretty (Halt t v) =
    PP.nest 2 $
      PP.sep
        [pretty ("halt" :: T.Text) <> brackets [pretty t], parens [pretty v]]


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


instance PP.Pretty Decl where
  pretty (Bind x v) = prettyDecl (pretty x) (pretty v)
  pretty (At x i v) =
    prettyDecl
      (pretty x)
      (pretty ("at" :: T.Text) <+> pretty i <+> pretty v)
  pretty (Arith x p v1 v2) =
    prettyDecl
      (pretty x)
      (PP.sep [parens [pretty v1], pretty p <+> parens [pretty v2]])
  pretty (Unpack a x v) =
    prettyDecl
      (brackets [pretty a, pretty x])
      (pretty ("unpack" :: T.Text) <+> parens [pretty v])
  pretty (Malloc x ts) =
    prettyDecl
      (pretty x)
      (pretty ("malloc" :: T.Text) <+> brackets (fmap pretty ts))
  pretty (Update x v1 i v2) =
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


instance Fv Tm where
  fv (Let (Bind x v) e) = fv v <> fv e & at x .~ Nothing
  fv (Let (At x _i v) e) = fv v <> fv e & at x .~ Nothing
  fv (Let (Arith x _p v1 v2) e) = fv v1 <> fv v2 <> fv e & at x .~ Nothing
  fv (Let _d _e) = error "No need"
  fv (App v _ts vs) = fv v <> foldMap fv vs
  fv (If0 v e1 e2) = fv v <> fv e1 <> fv e2
  fv (Halt _t v) = fv v


instance Ftv Tm where
  ftv (Let d e) = ftv d <> ftv e
  ftv (App v ts vs) = ftv v <> foldMap ftv ts <> foldMap ftv vs
  ftv (If0 v e1 e2) = ftv v <> ftv e1 <> ftv e2
  ftv (Halt t v) = ftv t <> ftv v


instance Ftv Decl where
  ftv (Bind _x v) = ftv v
  ftv (At _x _i v) = ftv v
  ftv (Arith _x _p v1 v2) = ftv v1 <> ftv v2
  ftv _ = error "no need"


-- | H, A: p
data Prog where
  LetRec :: HM.HashMap Name Ann -> Tm -> Prog


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
                  (HM.toList xs)
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
