module SF2TAL.Middle.FromK
  ( cProg
  )
where

import Control.Monad
import Control.Monad.Writer
import Data.Map qualified as M
import Data.Set qualified as S
import Lens.Micro.Platform
import SF2TAL.Middle.Middle
import SF2TAL.Utils


errorK :: Show a => a -> b
errorK x = error $ "not in K: " <> show x


type CT m = WriterT (M.Map Name Ann) m


cTy :: MonadUniq m => Ty -> CT m Ty
cTy (TVar a) = pure $ TVar a
cTy TInt = pure TInt
cTy (TFix as ts) = do
  b <- fresh
  ts' <- traverse cTy ts
  pure $ TExists b $ tTuple [TFix as (TVar b : ts'), TVar b]
cTy (TTuple ts) = TTuple <$> traverseOf (each . _1) cTy ts
cTy t@TExists{} = error $ "not in K: " <> show t


cProg :: MonadUniq m => Tm -> m Prog
cProg p = do
  (e, xs) <- runWriterT $ cExp p
  pure $ LetRec xs e


cExp :: MonadUniq m => Tm -> CT m Tm
cExp (Let d e) = Let <$> cDec d <*> cExp e
cExp (App v ts vs) = do
  z <- fresh
  v' <- cVal v
  zCode <- fresh
  zEnv <- fresh
  ts' <- traverse cTy ts
  vs' <- traverse cVal vs
  cTy (v ^. ty) >>= \case
    TExists b (TTuple [(tCode, _), (b', _)]) -> do
      when (TVar b /= b') $ error "cExp: b /= b'"
      pure $
        Let (Unpack b z v') $
          Let (At zCode 1 (Var z `Ann` tTuple [tCode, TVar b])) $
            Let (At zEnv 2 (Var z `Ann` tTuple [tCode, TVar b])) $
              App
                ((Var zCode `Ann` tCode) `appT` ts')
                []
                ([Var zEnv `Ann` TVar b] <> vs')
    t -> error $ "not TExists: " <> show t
cExp (If0 v e1 e2) = If0 <$> cVal v <*> cExp e1 <*> cExp e2
cExp (Halt t v) = Halt <$> cTy t <*> cVal v


cDec :: MonadUniq m => Decl -> CT m Decl
cDec (Bind x v) = Bind x <$> cVal v
cDec (At x i v) = At x i <$> cVal v
cDec (Arith x p v1 v2) = Arith x p <$> cVal v1 <*> cVal v2
cDec d@Unpack{} = errorK d
cDec d@Malloc{} = errorK d
cDec d@Update{} = errorK d


cVal :: MonadUniq m => Ann -> CT m Ann
cVal v@(u `Ann` t) = case u of
  Var x -> Ann (Var x) <$> cTy t
  IntLit i -> Ann (IntLit i) <$> cTy t
  Tuple vs -> Ann <$> (Tuple <$> traverse cVal vs) <*> cTy t
  Fix x as xs e -> do
    ts' <- traverse (cTy . snd) xs
    zCode <- fresh
    zEnv <- fresh
    let ys = fv v
    let bs = S.toList $ ftv v
    tEnv <- cTy $ tTuple $ M.elems ys
    let tRawCode = TFix (bs <> as) (tEnv : ts')
    let tCode = TFix as (tEnv : ts')
    e' <- cExp e
    t' <- cTy t
    let pack =
          Pack
            tEnv
            ( Tuple
                [ (Var zCode `Ann` tRawCode) `appT` fmap TVar bs
                , Var zEnv `Ann` tEnv
                ]
                `Ann` tTuple [tCode, tEnv]
            )
            t'
            `Ann` t'
    let vCode =
          Fix
            Nothing
            (bs <> as)
            ((zEnv, tEnv) : zip (fmap fst xs) ts')
            ( maybe id (\x' -> Let $ Bind x' pack) x $
                foldr
                  (\(i, y) -> Let (At y i (Var zEnv `Ann` tEnv)))
                  e'
                  (zip [1 ..] (M.keys ys))
            )
            `Ann` tRawCode
    vEnv <- Tuple <$> mapM (\(y, s) -> Ann (Var y) <$> cTy s) (M.toList ys)
    writer
      ( Pack
          tEnv
          ( Tuple
              [ (Var zCode `Ann` tRawCode) `appT` fmap TVar bs
              , vEnv `Ann` tEnv
              ]
              `Ann` tTuple [tCode, tEnv]
          )
          t'
          `Ann` t'
      , M.singleton zCode vCode
      )
  e@AppT{} -> errorK e
  e@Pack{} -> errorK e
