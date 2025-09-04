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


type Call = [Ty] -> [Val] -> KName -> Tm


newtype CEnv = CEnv
  { knownCls :: M.Map Name Call
  }


$(makeFieldsId 'CEnv)


type C es =
  ( Uniq :> es
  , Writer (M.Map Name Data) :> es
  , Reader CEnv :> es
  )


cTy :: C es => Ty -> Eff es Ty
cTy = \case
  TVar a -> pure $ TVar a
  TInt -> pure TInt
  TFix as ts t -> do
    b <- freshName
    ts' <- traverse cTy ts
    t' <- cTy t
    pure $ TExists b $ TTuple [TFix as (TVar b : ts') t', TVar b]
  TTuple ts -> TTuple <$> traverse cTy ts
  TExists a t -> TExists a <$> cTy t


cProg :: Uniq :> es => Tm -> Eff es TopLevel
cProg e = do
  (e', xs) <- runWriter $ runReader (CEnv{knownCls = mempty}) do
    cExp e
  pure $
    TopLevel (M.insert (Name "sf2talMain" 0) (Abs [] [] (Name "k" 0) TInt e') xs)


data DataW = DataW
  { cls :: M.Map Name Data
  , knownCls :: M.Map Name Call
  , substs :: M.Map Name Val
  }


instance Semigroup DataW where
  DataW c1 k1 s1 <> DataW c2 k2 s2 =
    DataW (c1 <> c2) (k1 <> k2) (s1 <> s2)


instance Monoid DataW where
  mempty = DataW mempty mempty mempty
  mappend = (<>)


cData ::
  (C es, Writer DataW :> es) =>
  Name ->
  Name ->
  Ty ->
  Data ->
  Eff es (Name, (Tm -> Tm) -> Data)
cData x vEnv tEnv = \case
  v@(Abs as xs k tk e) -> do
    ts' <- traverse (cTy . snd) xs
    let bs = S.toList $ ftv v
    let eVCode withEnv = Abs (bs <> as) ((vEnv, tEnv) : zip (fmap fst xs) ts') k tk do
          withEnv e
    let tRawCode = TFix (bs <> as) (tEnv : ts') tk
    vCode <- Name (prettyText x <> ".zCode") <$> fresh
    cl' <- freshName
    tv <- cTy (tyOf v)
    let dCl' =
          Tuple [Var vCode tRawCode `appT` fmap TVar bs, Var vEnv tEnv]
    let cl = Pack tEnv (Var cl' $ TTuple [tRawCode, tEnv]) tv
    zEnv <- Name "zEnv" <$> fresh
    let call ts vs k' =
          Let (Rec $ M.singleton zEnv $ Tuple []) $
            App
              ((Var vCode tRawCode `appT` fmap TVar bs) `appT` ts)
              []
              (Var zEnv (TTuple []) : vs)
              k'
    tell $
      DataW
        { cls = M.singleton cl' dCl'
        , knownCls = M.singleton x call
        , substs = M.singleton x cl
        }
    pure (vCode, eVCode)
  Tuple vs -> pure (x, const $ Tuple vs)


cExp :: C es => Tm -> Eff es Tm
cExp = \case
  Let (Rec fs) e1 -> do
    fs' <- forM fs \case
      Abs as xs' k tk e -> Abs as xs' k tk <$> cExp e
      Tuple ts -> pure $ Tuple ts
    let fvs = M.toList $ fv $ Let (Rec fs') e1
    vEnv <- Name "vEnv" <$> fresh
    dVEnv <- Tuple <$> mapM (\(y, s) -> Var y <$> cTy s) fvs
    tEnv <- TTuple <$> traverse (cTy . snd) fvs
    let withZEnv e' =
          foldr
            (\(i, y) -> Let (At y i $ Var vEnv tEnv))
            e'
            (zip [0 ..] $ fmap fst fvs)
    (fs'', DataW cls known sub) <- runWriter do
      (`M.traverseWithKey` fs') \x d -> cData x vEnv tEnv d
    let binds e' = foldr (\(x, v) -> Let $ Bind x v) e' $ M.toList sub
    forM_ fs'' \(vCode, eVCode) ->
      tell $ M.singleton vCode $ eVCode $ Let (Rec cls) . binds . withZEnv
    let known' = if null fvs then known else mempty
    local (knownCls <>~ known') do
      Let (Rec $ M.insert vEnv dVEnv cls) . binds <$> cExp e1
  Let d e -> Let <$> cDec d <*> cExp e
  AppK k v -> AppK k <$> cVal v
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
                      Let (At zCode 0 $ Var z (TTuple [tCode, TVar b])) $
                        Let (At zEnv 1 $ Var z (TTuple [tCode, TVar b])) $
                          App
                            (Var zCode tCode `appT` ts')
                            []
                            ([Var zEnv (TVar b)] <> vs')
                            k
                t' -> error $ "not TExists: " <> show t'
    | otherwise -> error "Calling non-variable value in K"
  If v k1 k2 -> If <$> cVal v <*> pure k1 <*> pure k2
  Meta m e -> Meta m <$> cExp e


cDec :: C es => Decl -> Eff es Decl
cDec = \case
  Bind x v -> Bind x <$> cVal v
  BindK x k t e -> BindK x k t <$> cExp e
  At x i v -> At x i <$> cVal v
  BinOp x p v1 v2 -> BinOp x p <$> cVal v1 <*> cVal v2
  d@Rec{} -> errorK d
  d@Unpack{} -> errorK d


cVal :: C es => Val -> Eff es Val
cVal = \case
  Var x t -> Var x <$> cTy t
  IntLit i -> pure $ IntLit i
  e@AppT{} -> errorK e
  e@Pack{} -> errorK e
