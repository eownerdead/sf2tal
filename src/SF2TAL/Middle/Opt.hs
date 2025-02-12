module SF2TAL.Middle.Opt
  ( simp
  )
where

import Data.Map qualified as M
import Effectful
import SF2TAL.F (Prim (..))
import SF2TAL.Middle
import SF2TAL.Uniq
import SF2TAL.Utils


type Occurs = M.Map Name Int


oUnion :: Occurs -> Occurs -> Occurs
oUnion = M.unionWith (+)


oUnions :: [Occurs] -> Occurs
oUnions = foldr oUnion mempty


occurs :: SubVals a => a -> Occurs
occurs e =
  oUnions
    [ M.singleton x 1
    | Var x _t <- universeOnOf subVals subVals e
    ]


occursOf :: SubVals a => Name -> a -> Int
occursOf x e = M.findWithDefault x 0 (occurs e)


class Size a where
  size :: a -> Int


instance Size Val where
  size = \case
    Var _x _t -> 0
    IntLit _ -> 0
    Fix _x _as xs e -> 1 + length xs + size e
    Tuple vs -> 1 + sum (fmap ((1 +) . size) vs)
    AppT v _t -> size v
    _ -> error "No need"


instance Size Tm where
  size = \case
    Let (Bind _x v) e -> 1 + size v + size e
    Let (At _x _i v) e -> 1 + size v + size e
    Let (Arith _x _p v1 v2) e -> 1 + size v1 + size v2 + size e
    Let (Unpack _a _x v) e -> 1 + size v + size e
    App v _ts vs -> 1 + size v + sum (fmap size vs)
    If0 v e1 e2 -> 1 + size v + size e1 + size e2
    Halt v -> 1 + size v
    _ -> error "No need"


threshold :: Int
threshold = 100


simp :: Uniq :> es => Tm -> Eff es Tm
simp = tm


tm :: Uniq :> es => Tm -> Eff es Tm
tm = \case
  Let (Bind x v) e
    | n == 0 -> tm e
    | n == 1 || sz * n < threshold -> do
        v' <- val v
        tm =<< subst (M.singleton x v') e
    where
      n = occursOf x e
      sz = size v
  Let (Arith x p (IntLit n) (IntLit m)) e -> do
    e' <- subst (M.singleton x (IntLit n')) e
    tm e'
    where
      n' = case p of
        Add -> n + m
        Mul -> n * m
        Sub -> n - m
  Let d e -> Let <$> subVals val d <*> tm e
  App v ts vs -> do
    vs' <- traverse val vs
    val v >>= \case
      Fix Nothing as xs e ->
        let e' = foldr (uncurry tsubst) e (zip as ts)
        in pure $ foldr (\(x, v') -> Let (Bind x v')) e' (zip (fmap fst xs) vs')
      v' -> pure $ App v' ts vs'
  If0 v e1 e2 ->
    val v >>= \case
      IntLit i
        | i == 0 -> tm e1
        | otherwise -> tm e2
      v' -> If0 v' <$> tm e1 <*> tm e2
  Halt v -> Halt <$> val v


val :: Uniq :> es => Val -> Eff es Val
val = subVals \case
  Fix x as xs e
    | Just x' <- x
    , occursOf x' e /= 0 ->
        Fix x as xs <$> tm e
    | otherwise -> Fix Nothing as xs <$> tm e
  v -> val v
