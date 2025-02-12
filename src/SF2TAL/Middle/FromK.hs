module SF2TAL.Middle.FromK
  ( cProg
  )
where

import Control.Monad
import Data.Map qualified as M
import Data.Set qualified as S
import Effectful
import Effectful.Writer.Static.Local
import Lens.Micro.Platform
import SF2TAL.Middle.Middle
import SF2TAL.Uniq


errorK :: Show a => a -> b
errorK x = error $ "not in K: " <> show x


type C es = (Uniq :> es, Writer (M.Map Name Val) :> es)


cTy :: C es => Ty -> Eff es Ty
cTy = \case
  TVar a -> pure $ TVar a
  TInt -> pure TInt
  TFix as ts -> do
    b <- fresh
    ts' <- traverse cTy ts
    pure $ TExists b $ tTuple [TFix as (TVar b : ts'), TVar b]
  TTuple ts -> TTuple <$> traverseOf (each . _1) cTy ts
  t@TExists{} -> error $ "not in K: " <> show t


cProg :: Uniq :> es => Tm -> Eff es Prog
cProg p = do
  (e, xs) <- runWriter do cExp p
  pure $ LetRec xs e


cExp :: C es => Tm -> Eff es Tm
cExp = \case
  Let d e -> Let <$> cDec d <*> cExp e
  App v ts vs -> do
    z <- fresh
    v' <- cVal v
    zCode <- fresh
    zEnv <- fresh
    ts' <- traverse cTy ts
    vs' <- traverse cVal vs
    cTy (ty v) >>= \case
      TExists b (TTuple [(tCode, _), (b', _)]) -> do
        when (TVar b /= b') do error "cExp: b /= b'"
        pure $
          Let (Unpack b z v') $
            Let (At zCode 1 $ Var z (tTuple [tCode, TVar b])) $
              Let (At zEnv 2 $ Var z (tTuple [tCode, TVar b])) $
                App
                  (Var zCode tCode `appT` ts')
                  []
                  ([Var zEnv (TVar b)] <> vs')
      t -> error $ "not TExists: " <> show t
  If0 v e1 e2 -> If0 <$> cVal v <*> cExp e1 <*> cExp e2
  Halt v -> Halt <$> cVal v


cDec :: C es => Decl -> Eff es Decl
cDec = \case
  Bind x v -> Bind x <$> cVal v
  At x i v -> At x i <$> cVal v
  Arith x p v1 v2 -> Arith x p <$> cVal v1 <*> cVal v2
  d@Unpack{} -> errorK d
  d@Malloc{} -> errorK d
  d@Update{} -> errorK d


cVal :: C es => Val -> Eff es Val
cVal = \case
  Var x t -> Var x <$> cTy t
  IntLit i -> pure $ IntLit i
  Tuple vs -> Tuple <$> traverse cVal vs
  v@(Fix x as xs e) -> do
    ts' <- traverse (cTy . snd) xs
    zCode <- fresh
    zEnv <- fresh
    let ys = fv v
    let bs = S.toList $ ftv v
    tEnv <- cTy $ tTuple $ M.elems ys
    let tRawCode = TFix (bs <> as) (tEnv : ts')
    e' <- cExp e
    t' <- cTy $ ty v
    let pack =
          Pack
            tEnv
            do
              Tuple
                [ Var zCode tRawCode `appT` fmap TVar bs
                , Var zEnv tEnv
                ]
            t'
    let vCode =
          Fix
            Nothing
            (bs <> as)
            ((zEnv, tEnv) : zip (fmap fst xs) ts')
            do
              maybe id (\x' -> Let $ Bind x' pack) x $
                foldr
                  do \(i, y) -> Let (At y i (Var zEnv tEnv))
                  e'
                  (zip [1 ..] (M.keys ys))
    vEnv <- Tuple <$> mapM (\(y, s) -> Var y <$> cTy s) (M.toList ys)
    tell $ M.singleton zCode vCode
    pure $
      Pack
        tEnv
        ( Tuple
            [ Var zCode tRawCode `appT` fmap TVar bs
            , vEnv
            ]
        )
        t'
  e@AppT{} -> errorK e
  e@Pack{} -> errorK e
