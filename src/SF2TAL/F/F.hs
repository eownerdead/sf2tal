module SF2TAL.F.F
  ( TName
  , Name
  , Ty (..)
  , tsubst
  , (#->)
  , Tm (..)
  , (#$)
  , Prim (..)
  , (#+)
  , (#-)
  , (#*)
  , ann
  )
where

import Data.Text qualified as T
import Prettyprinter


type TName = T.Text


type Name = T.Text


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


tsubst :: TName -> Ty -> Ty -> Ty
tsubst a t' (TVar b)
  | a == b = t'
  | otherwise = TVar b
tsubst _ _ TInt = TInt
tsubst a t' (t1 `TFun` t2) = tsubst a t' t1 `TFun` tsubst a t' t2
tsubst a t' (TForall b t)
  | a == b = TForall b t
  | otherwise = TForall b (tsubst a t' t)
tsubst a t' (TTuple ts) = TTuple $ fmap (tsubst a t') ts


infixr 5 `TFun`


infixr 5 #->


(#->) :: Ty -> Ty -> Ty
(#->) = TFun


-- | u
data Tm where
  -- | x
  Var :: Name -> Tm
  -- | i
  IntLit :: Int -> Tm
  -- | fix x(x1: t1): t2. e
  Fix :: Name -> Name -> Ty -> Ty -> Tm -> Tm
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


infixl 9 `App`


infixl 9 #$


(#$) :: Tm -> Tm -> Tm
(#$) = App


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


instance Pretty Prim where
  pretty Add = "+"
  pretty Sub = "-"
  pretty Mul = "*"


infixl 6 #+


(#+) :: Tm -> Tm -> Tm
(#+) = Arith Add


infixl 6 #-


(#-) :: Tm -> Tm -> Tm
(#-) = Arith Sub


infixl 7 #*


(#*) :: Tm -> Tm -> Tm
(#*) = Arith Mul


ann :: Tm -> Ty
ann (Ann _e t) = t
ann x = error $ "unannotated: " <> show x
