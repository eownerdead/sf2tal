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
tmCntUsed = \case
  Let d e -> declCntUsed d `cntUnion` tmCntUsed e
  App v _as vs -> cntUnions (annCntUsed v : fmap annCntUsed vs)
  If0 v e1 e2 -> cntUnions [annCntUsed v, tmCntUsed e1, tmCntUsed e2]
  Halt _t v -> annCntUsed v


annCntUsed :: Ann -> Cnt
annCntUsed (u `Ann` _) = case u of
  Var x -> M.singleton x 1
  IntLit _ -> mempty
  Fix _x _xs _as e -> tmCntUsed e
  Tuple vs -> cntUnions $ fmap annCntUsed vs
  AppT v _t -> annCntUsed v
  Pack _t1 v _t2 -> annCntUsed v


declCntUsed :: Decl -> Cnt
declCntUsed = \case
  At _x _i v -> annCntUsed v
  Arith _x _p v1 v2 -> annCntUsed v1 `cntUnion` annCntUsed v2
  _ -> error "No need"


type Simp = Reader Cnt


simp :: Tm -> Tm
simp t = runReader (tmSimp t) (tmCntUsed t)


tmSimp :: Tm -> Simp Tm
tmSimp = \case
  Let (Arith x p (IntLit n `Ann` _) (IntLit m `Ann` _)) e ->
    tmSimp $ subst x (IntLit n' `Ann` TInt) e
    where
      n' = case p of
        Add -> n + m
        Mul -> n * m
        Sub -> n - m
  Let d e -> Let <$> declSimp d <*> tmSimp e
  App v as vs ->
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
  If0 v e1 e2 -> If0 <$> annSimp v <*> tmSimp e1 <*> tmSimp e2
  Halt t v -> Halt t <$> annSimp v


annSimp :: Ann -> Simp Ann
annSimp (u `Ann` t) = (`Ann` t) <$> valSimp u


valSimp :: Val -> Simp Val
valSimp = \case
  Var x -> pure $ Var x
  IntLit i -> pure $ IntLit i
  Fix x xs as e
    | Just x' <- x ->
        preview (ix x') >>= \case
          Nothing -> Fix Nothing xs as <$> tmSimp e
          _ -> Fix x xs as <$> tmSimp e
    | otherwise -> Fix Nothing xs as <$> tmSimp e
  Tuple vs -> Tuple <$> traverse annSimp vs
  _ -> error "No need"


declSimp :: Decl -> Simp Decl
declSimp = \case
  At x i v -> At x i <$> annSimp v
  Arith x p v1 v2 -> Arith x p <$> annSimp v1 <*> annSimp v2
  _ -> error "No need"
