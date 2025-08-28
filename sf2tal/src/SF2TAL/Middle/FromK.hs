module SF2TAL.Middle.FromK
  ( cProg
  )
where

import Data.Map qualified as M
import Data.Set qualified as S
import Effectful.Reader.Static.Microlens
import Effectful.Writer.Static.Local
import SF2TAL.Middle.Middle
import SF2TAL.PP
import SF2TAL.Prelude


errorK :: Show a => a -> b
errorK x = error $ "not in K: " <> show x


type KnowCl = [Ty] -> [Val] -> KName -> Tm


newtype CEnv = CEnv {knownCls :: M.Map Name KnowCl}


$(makeFieldsId 'CEnv)


type C es = (Uniq :> es, Writer (M.Map Name Abs) :> es, Reader CEnv :> es)


cTy :: C es => Ty -> Eff es Ty
cTy = \case
  TVar a -> pure $ TVar a
  TInt -> pure TInt
  TFix as ts t -> do
    b <- fresh
    ts' <- traverse cTy ts
    t' <- cTy t
    pure $ TExists b $ TTuple [TFix as (TVar b : ts') t', TVar b]
  TTuple ts -> TTuple <$> traverse cTy ts
  TExists a t -> TExists a <$> cTy t


cProg :: Uniq :> es => Tm -> Eff es Tm
cProg p = do
  (e, xs) <- runWriter $ runReader (CEnv{knownCls = mempty}) do cExp p
  pure $ Let (Rec xs) e


cExp :: C es => Tm -> Eff es Tm
cExp = \case
  Let (Rec fs) e1 -> do
    fs' <- traverse (\(Abs as xs' k tk e) -> Abs as xs' k tk <$> cExp e) fs
    let fvs = M.toList $ fv $ Let (Rec fs') e1
    vEnv <- Name "vEnv" <$> fresh
    dVEnv <- CTuple vEnv <$> mapM (\(y, s) -> Var y <$> cTy s) fvs
    tEnv <- TTuple <$> traverse (cTy . snd) fvs
    let withZEnv e' =
          foldr
            (\(i, y) -> Let (At y i $ Var vEnv tEnv))
            e'
            (zip [1 ..] $ fmap fst fvs)
    fs'' <- (`M.traverseWithKey` fs') \x v@(Abs as xs' k tk e) -> do
      ts' <- traverse (cTy . snd) xs'
      let bs = S.toList $ ftv v
      let eVCode withCls = Abs (bs <> as) ((vEnv, tEnv) : zip (fmap fst xs') ts') k tk do
            withCls $ withZEnv e
      let tRawCode = TFix (bs <> as) (tEnv : ts') tk
      vCode <- Name (prettyText x <> ".zCode") <$> fresh
      cl <- freshName
      tv <- cTy (tyOf v)
      let packCl =
            Let (CTuple cl [Var vCode tRawCode `appT` fmap TVar bs, Var vEnv tEnv])
              . Let (Bind x (Pack tEnv (Var cl $ TTuple [tRawCode, tEnv]) tv))
      zEnv <- Name "zEnv" <$> fresh
      let call ts vs k' =
            Let (CTuple zEnv []) $
              App
                ((Var vCode tRawCode `appT` fmap TVar bs) `appT` ts)
                []
                (Var zEnv (TTuple []) : vs)
                k'
      pure (vCode, eVCode, packCl, call)
    let packCls e = foldr (\(_, _, v, _) -> v) e fs''
    forM_ fs'' \(vCode, eVCode, _, _) -> tell $ M.singleton vCode (eVCode packCls)
    local
      (knownCls <>~ if null fvs then fmap (\(_, _, _, call) -> call) fs'' else mempty)
      do
        Let dVEnv . packCls <$> cExp e1
  Let d e -> Let <$> cDec d <*> cExp e
  AppK k v -> pure $ AppK k v
  App v ts vs k
    | Var f t <- v -> do
        v' <- cVal v
        ts' <- traverse cTy ts
        vs' <- traverse cVal vs
        call' <- preview (knownCls . ix f)
        if
          | Just call <- call' -> pure $ call ts' vs' k
          | otherwise ->
              cTy t >>= \case
                TExists b (TTuple [tCode, b']) -> do
                  z <- Name "z" <$> fresh
                  zCode <- Name "zCode" <$> fresh
                  zEnv <- Name "zEnv" <$> fresh
                  when (TVar b /= b') do error "cExp: b /= b'"
                  pure $
                    Let (Unpack b z v') $
                      Let (At zCode 1 $ Var z (TTuple [tCode, TVar b])) $
                        Let (At zEnv 2 $ Var z (TTuple [tCode, TVar b])) $
                          App
                            (Var zCode tCode `appT` ts')
                            []
                            ([Var zEnv (TVar b)] <> vs')
                            k
                t' -> error $ "not TExists: " <> show t'
    | otherwise -> error "Calling non-variable value in K"
  If v k1 k2 -> If <$> cVal v <*> pure k1 <*> pure k2
  Halt v -> Halt <$> cVal v
  Loc l e -> Loc l <$> cExp e


cDec :: C es => Decl -> Eff es Decl
cDec = \case
  Bind x v -> Bind x <$> cVal v
  BindK x k t e -> BindK x k t <$> cExp e
  At x i v -> At x i <$> cVal v
  BinOp x p v1 v2 -> BinOp x p <$> cVal v1 <*> cVal v2
  d@Rec{} -> errorK d
  d@Unpack{} -> errorK d
  CTuple x vs -> CTuple x <$> traverse cVal vs


cVal :: C es => Val -> Eff es Val
cVal = \case
  Var x t -> Var x <$> cTy t
  IntLit i -> pure $ IntLit i
  e@AppT{} -> errorK e
  e@Pack{} -> errorK e
