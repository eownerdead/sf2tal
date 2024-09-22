module SF2TAL.Middle
  ( Fv (..)
  , Ftv (..)
  , Ty (..)
  , tTupleInitN
  , tTupleInitToN
  , tTuple
  , tTupleUninited
  , tExists
  , Val (..)
  , appT
  , Ann (..)
  , val
  , ty
  , Decl (..)
  , ckProg
  , ckTm
  , Tm (..)
  , Prog (..)
  )
where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.HashMap.Strict qualified as HM
import Data.HashSet qualified as HS
import Data.Text qualified as T
import Lens.Micro.Platform
import Prettyprinter (pretty, (<+>))
import Prettyprinter qualified as PP
import SF2TAL.Common
import SF2TAL.F (Prim)


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


tTupleInitToN :: Int -> Ty -> Ty
tTupleInitToN i ts = foldr tTupleInitN ts [1 .. i]


tTuple :: [Ty] -> Ty
tTuple = TTuple . fmap (,True)


tTupleUninited :: [Ty] -> Ty
tTupleUninited = TTuple . fmap (,False)


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


type Env = HM.HashMap Name Ty


type Tc = ReaderT Env (Either T.Text)


lookupVar :: Name -> Tc Ty
lookupVar x = do
  env <- ask
  if
    | Just t <- env ^? ix x -> pure t
    | otherwise -> throwError $ "unknown variable " <> x


ckProg :: Prog -> Either T.Text ()
ckProg p = runReaderT (ckProg' p) mempty


ckProg' :: Prog -> Tc ()
ckProg' (LetRec xs e) = local (fmap (^. ty) xs <>) $ do
  mapM_ ckAnn xs
  ckTm' e


ckTm :: Tm -> Either T.Text ()
ckTm e = runReaderT (ckTm' e) mempty


ckTm' :: Tm -> Tc ()
ckTm' (Let d e) = do
  ckDecl d $ ckTm' e
ckTm' (App v bs vs)
  | TFix as ts <- v ^. ty = forM_ (zip ts vs) $ \(t, v') -> do
      let t' = foldr (uncurry tsubst) t (zip as bs)
      when (v' ^. ty /= t') $
        throwError $
          "App: vs does not match: " <> prettyText (v' ^. ty)
  | otherwise = throwError $ "App: v is not TFix, but " <> prettyText (v ^. ty)
ckTm' (If0 v e1 e2) = do
  when (v ^. ty /= TInt) $
    throwError $
      "If0: v is not TInt, but " <> prettyText (v ^. ty)
  ckTm' e1
  ckTm' e2
ckTm' (Halt t v) =
  when (v ^. ty /= t) $
    throwError $
      "Halt: v is not t, but " <> prettyText (v ^. ty)


ckDecl :: Decl -> Tc a -> Tc a
ckDecl (Bind x v) k = do
  ckAnn v
  local (at x ?~ v ^. ty) k
ckDecl (At x i v) k
  | TTuple ts <- v ^. ty
  , Just t <- ts ^? ix (i - 1) = do
      ckAnn v
      local (at x ?~ fst t) k
  | otherwise =
      throwError $ "At: v is not TTuple or invalid i: " <> prettyText (v ^. ty)
ckDecl (Arith x _p v1 v2) k = do
  ckAnn v1
  ckAnn v2
  when (v1 ^. ty /= TInt) $
    throwError $
      "Arith: v1 is not TInt, but " <> prettyText (v1 ^. ty)
  when (v2 ^. ty /= TInt) $
    throwError $
      "Arith: v2 is not TInt, but " <> prettyText (v2 ^. ty)
  local (at x ?~ TInt) k
ckDecl (Unpack a x v) k
  | TExists a' t <- v ^. ty = do
      ckAnn v
      local (at x ?~ tsubst a' (TVar a) t) k
  | otherwise =
      throwError $ "Unpack: v is not TExists, but " <> prettyText (v ^. ty)
ckDecl (Malloc x ts) k = local (at x ?~ tTupleUninited ts) k
ckDecl (Update x v1 i v2) k
  | TTuple ts <- v1 ^. ty
  , Just (t, _) <- ts ^? ix (i - 1) = do
      ckAnn v1
      ckAnn v2
      when (v2 ^. ty /= t) $
        throwError $
          "Update: type of v2 does not match: " <> prettyText (v2 ^. ty)
      local (at x ?~ tTupleInitN i (v1 ^. ty)) k
  | otherwise =
      throwError $
        "Update: v1 is not Tuple or invalid i: " <> prettyText (v1 ^. ty)


ckAnn :: Ann -> Tc ()
ckAnn (u `Ann` t) = case u of
  Var x -> do
    t' <- lookupVar x
    when (t /= t') $
      throwError $
        "Var: Ann: " <> prettyText u
  IntLit _ ->
    when (t /= TInt) $
      throwError $
        "IntLit: Ann is not TInt, but " <> prettyText t
  Fix x _as xs e ->
    if
      | TFix _as' _ts <- t ->
          local ((HM.fromList xs & at x ?~ t) <>) $ ckTm' e
      | otherwise -> throwError $ "Fix: Ann is not TFix, but " <> prettyText t
  Tuple vs -> do
    mapM_ ckAnn vs
    when (tTuple (fmap (^. ty) vs) /= t) $
      throwError $
        "Tuple: Ann not match: " <> prettyText t
  v `AppT` t' ->
    if
      | TFix (a : as) ts <- v ^. ty -> do
          ckAnn v
          when (TFix as (tsubst a t' <$> ts) /= t) $
            throwError $
              "AppT: Ann not match: " <> prettyText t
      | otherwise -> throwError $ "AppT: v is not TFix, but " <> prettyText t
  Pack t1 v t2 ->
    if
      | TExists a t2' <- t2 -> do
          ckAnn v
          when (t2 /= t) $ throwError $ "Pack: Ann not match: " <> prettyText t
          when (v ^. ty /= tsubst a t1 t2') $
            throwError $
              "Pack: Invalid v: " <> prettyText (tsubst a t1 t2')
      | otherwise ->
          throwError $ "Pack: t2 is not TExists, but " <> prettyText t2
