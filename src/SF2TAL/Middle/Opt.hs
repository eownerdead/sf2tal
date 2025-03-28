module SF2TAL.Middle.Opt
  ( simp
  )
where

import Data.Map qualified as M
import Effectful
import SF2TAL.F (Prim (..))
import SF2TAL.Middle
import SF2TAL.Name
import SF2TAL.Plate
import SF2TAL.Uniq


type Occurs = M.Map Name Int


newtype OMap = OMap Occurs


instance Semigroup OMap where
  OMap x <> OMap y = OMap $ M.unionWith (+) x y


instance Monoid OMap where
  mempty = OMap mempty


occurs :: ProjOf Plate a => a -> Occurs
occurs e = oc
  where
    OMap oc = foldFor (preFold $ purePlate{pVal}) e
    pVal = \case
      Var x _ -> Const $ OMap $ M.singleton x 1
      _ -> Const mempty


occursOf :: ProjOf Plate a => Name -> a -> Int
occursOf x e = M.findWithDefault 0 x (occurs e)


class Size a where
  size :: a -> Int


instance Size Val where
  size = \case
    Var _x _t -> 0
    IntLit _ -> 0
    Abs _as xs e -> 1 + length xs + size e
    Tuple vs -> 1 + sum (fmap ((1 +) . size) vs)
    AppT v _t -> size v
    _ -> error "No need"


instance Size Tm where
  size = \case
    Let (Bind _x v) e -> 1 + size v + size e
    Let (At _x _i v) e -> 1 + size v + size e
    Let (Arith _x _p v1 v2) e -> 1 + size v1 + size v2 + size e
    Let (Unpack _a _x v) e -> 1 + size v + size e
    LetRec xs e -> sum (fmap size xs) + size e
    App v _ts vs -> 1 + size v + sum (fmap size vs)
    If0 v e1 e2 -> 1 + size v + size e1 + size e2
    Halt v -> 1 + size v
    _ -> error "No need"


threshold :: Int
threshold = 10


inlineApp :: Uniq :> es => Name -> Val -> Tm -> Eff es Tm
inlineApp x (Abs as xs e) = traverseMFor $ postMap purePlate{pTm}
  where
    pTm = \case
      App (Var y _) ts vs
        | y == x ->
            let e' = foldr (uncurry tsubst) e (zip as ts)
            in pure $ foldr (\(x', v') -> Let (Bind x' v')) e' (zip (fmap fst xs) vs)
      e' -> pure e'
inlineApp _ _ = error "Value of letrec is not a function"


simp :: Uniq :> es => Tm -> Eff es Tm
simp = traverseMFor $ postMap purePlate{pTm}
  where
    pTm = \case
      Let (Arith x p (IntLit n) (IntLit m)) e -> do
        subst (M.singleton x (IntLit n')) e
        where
          n' = case p of
            Add -> n + m
            Mul -> n * m
            Sub -> n - m
      LetRec (M.toList -> []) e -> pure e
      LetRec xs@(M.toList -> [(x1, v1)]) e ->
        case (occursOf x1 e, occursOf x1 v1) of
          (0, 0) -> pure e
          (1, 0) -> LetRec xs <$> inlineApp x1 v1 e
          (_, _)
            | size v1 <= threshold -> LetRec xs <$> inlineApp x1 v1 e
            | otherwise -> pure $ LetRec xs e
      If0 v e1 e2 ->
        case v of
          IntLit i
            | i == 0 -> pure e1
            | otherwise -> pure e2
          v' -> pure $ If0 v' e1 e2
      e -> pure e
