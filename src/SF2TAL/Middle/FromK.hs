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
import SF2TAL.Name
import SF2TAL.PP
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


cProg :: Uniq :> es => Tm -> Eff es Tm
cProg p = do
  (e, xs) <- runWriter do cExp p
  pure $ LetRec xs e


cExp :: C es => Tm -> Eff es Tm
cExp = \case
  Let d e -> Let <$> cDec d <*> cExp e
  LetRec xs e1 -> do
    let fvs = M.toList $ fv $ LetRec xs e1
    vEnv <- Tuple <$> mapM (\(y, s) -> Var y <$> cTy s) fvs
    tEnv <- tTuple <$> traverse (cTy . snd) fvs
    zEnv <- freshName
    xs' <- forM xs \case
      v@(Abs as xs' e) -> do
        e' <- cExp e
        ts' <- traverse (cTy . snd) xs'
        let bs = S.toList $ ftv v
        let vCode k = Abs (bs <> as) ((zEnv, tEnv) : zip (fmap fst xs') ts') do
              foldr
                (\(i, y) -> Let (At y i $ Var zEnv tEnv))
                (k e')
                (zip [1 ..] $ fmap fst fvs)
        let tRawCode = TFix (bs <> as) (tEnv : ts')
        zCode <- freshName
        pack <-
          Pack
            tEnv
            (Tuple [Var zCode tRawCode `appT` fmap TVar bs, vEnv])
            <$> cTy (tyOf v)
        pure (zCode, vCode, pack)
      v -> errorK $ "value of LetRec is not Abs" <> docStr (pp v)
    let pack e = M.foldrWithKey (\x (_, _, v) -> Let (Bind x v)) e xs'
    forM_ xs' \(zCode, vCode, _) -> tell $ M.singleton zCode (vCode pack)
    pack <$> cExp e1
  App v ts vs -> do
    z <- freshName
    v' <- cVal v
    zCode <- freshName
    zEnv <- freshName
    ts' <- traverse cTy ts
    vs' <- traverse cVal vs
    cTy (tyOf v) >>= \case
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
  e@Abs{} -> error $ "Abs: " <> docStr (pp e)
  Tuple vs -> Tuple <$> traverse cVal vs
  e@AppT{} -> errorK e
  e@Pack{} -> errorK e
