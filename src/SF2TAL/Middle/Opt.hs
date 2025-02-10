module SF2TAL.Middle.Opt
  ( simp
  )
where

import Control.Monad.Reader
import Data.Map qualified as M
import Lens.Micro.Platform
import SF2TAL.F (Prim (..))
import SF2TAL.Middle
import SF2TAL.Utils


type Cnt = M.Map Name Int


cntUnion :: Cnt -> Cnt -> Cnt
cntUnion = M.unionWith (+)


cntUnions :: [Cnt] -> Cnt
cntUnions = foldr cntUnion mempty


cntUsed :: Tm -> Cnt
cntUsed e =
  cntUnions
    [ M.singleton x 1
    | Var x _t <- universeOnOf subVals subVals e
    ]


type Simp = Reader Cnt


simp :: Tm -> Tm
simp t = runReader (tmSimp t) (cntUsed t)


tmSimp :: Tm -> Simp Tm
tmSimp = \case
  Let (Arith x p (IntLit n) (IntLit m)) e ->
    tmSimp $ subst x (IntLit n') e
    where
      n' = case p of
        Add -> n + m
        Mul -> n * m
        Sub -> n - m
  Let d e -> Let <$> subVals annSimp d <*> tmSimp e
  App v as vs ->
    annSimp v >>= \case
      Fix Nothing [] [] e -> tmSimp e
      v'@(Fix Nothing [] ((x, _) : xs) e) ->
        view (at x) >>= \case
          Nothing -> tmSimp $ App (Fix Nothing [] xs e) [] (tail vs)
          Just 1 ->
            tmSimp $
              App (Fix Nothing [] xs (subst x (head vs) e)) [] (tail vs)
          _ -> App v' as <$> traverse annSimp vs
      v' -> App v' as <$> traverse annSimp vs
  If0 v e1 e2 -> If0 <$> annSimp v <*> tmSimp e1 <*> tmSimp e2
  Halt v -> Halt <$> annSimp v


annSimp :: Val -> Simp Val
annSimp = subVals \case
  Fix x xs as e
    | Just x' <- x ->
        preview (ix x') >>= \case
          Nothing -> Fix Nothing xs as <$> tmSimp e
          _ -> Fix x xs as <$> tmSimp e
    | otherwise -> Fix Nothing xs as <$> tmSimp e
  v -> annSimp v
