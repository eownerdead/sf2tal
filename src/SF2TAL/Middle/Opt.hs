module SF2TAL.Middle.Opt
  ( simp
  )
where

import Control.Monad.Reader
import Data.Map qualified as M
import Lens.Micro.Platform
import SF2TAL.F (Prim (..))
import SF2TAL.Middle


type Cnt = M.Map Name Int


cntUnion :: Cnt -> Cnt -> Cnt
cntUnion = M.unionWith (+)


cntUnions :: [Cnt] -> Cnt
cntUnions = foldr cntUnion mempty


tmCntUsed :: Tm -> Cnt
tmCntUsed (Let d e) = declCntUsed d `cntUnion` tmCntUsed e
tmCntUsed (App v _as vs) = cntUnions (annCntUsed v : fmap annCntUsed vs)
tmCntUsed (If0 v e1 e2) = cntUnions [annCntUsed v, tmCntUsed e1, tmCntUsed e2]
tmCntUsed (Halt _t v) = annCntUsed v


annCntUsed :: Ann -> Cnt
annCntUsed (u `Ann` _) = case u of
  Var x -> M.singleton x 1
  IntLit _ -> mempty
  Fix _x _xs _as e -> tmCntUsed e
  Tuple vs -> cntUnions $ fmap annCntUsed vs
  AppT v _t -> annCntUsed v
  Pack _t1 v _t2 -> annCntUsed v


declCntUsed :: Decl -> Cnt
declCntUsed (At _x _i v) = annCntUsed v
declCntUsed (Arith _x _p v1 v2) = annCntUsed v1 `cntUnion` annCntUsed v2
declCntUsed _ = error "No need"


type Simp = Reader Cnt


simp :: Tm -> Tm
simp t = runReader (tmSimp t) (tmCntUsed t)


tmSimp :: Tm -> Simp Tm
tmSimp (Let (Arith x p (IntLit n `Ann` _) (IntLit m `Ann` _)) e) =
  tmSimp $ subst x (IntLit n' `Ann` TInt) e
  where
    n' = case p of
      Add -> n + m
      Mul -> n * m
      Sub -> n - m
tmSimp (Let d e) = Let <$> declSimp d <*> tmSimp e
tmSimp (App v as vs) =
  annSimp v >>= \case
    Fix Nothing [] [] e `Ann` _ -> tmSimp e
    v'@(Fix Nothing [] ((x, _) : xs) e `Ann` t') ->
      view (at x) >>= \case
        Nothing -> tmSimp $ App (Fix Nothing [] xs e `Ann` t') [] (tail vs)
        Just 1 ->
          tmSimp $
            App (Fix Nothing [] xs (subst x (head vs) e) `Ann` t') [] (tail vs)
        _ -> App v' as <$> traverse annSimp vs
    v' -> App v' as <$> traverse annSimp vs
tmSimp (If0 v e1 e2) = If0 <$> annSimp v <*> tmSimp e1 <*> tmSimp e2
tmSimp (Halt t v) = Halt t <$> annSimp v


annSimp :: Ann -> Simp Ann
annSimp (u `Ann` t) = (`Ann` t) <$> valSimp u


valSimp :: Val -> Simp Val
valSimp (Var x) = pure $ Var x
valSimp (IntLit i) = pure $ IntLit i
valSimp (Fix x xs as e)
  | Just x' <- x =
      preview (ix x') >>= \case
        Nothing -> Fix Nothing xs as <$> tmSimp e
        _ -> Fix x xs as <$> tmSimp e
  | otherwise = Fix Nothing xs as <$> tmSimp e
valSimp (Tuple vs) = Tuple <$> traverse annSimp vs
valSimp _ = error "No need"


declSimp :: Decl -> Simp Decl
declSimp (At x i v) = At x i <$> annSimp v
declSimp (Arith x p v1 v2) = Arith x p <$> annSimp v1 <*> annSimp v2
declSimp _ = error "No need"
