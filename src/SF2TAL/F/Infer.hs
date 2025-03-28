module SF2TAL.F.Infer
  ( infer
  )
where

import Control.Exception.Safe
import Control.Monad
import Data.Foldable
import Data.Map qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Effectful
import Effectful.Reader.Static
import Effectful.Reader.Static.Microlens
import Effectful.State.Static.Local
import Effectful.State.Static.Local.Microlens
import GHC.Stack
import Lens.Micro.Platform hiding (preuse, preview, (.=))
import Prettyprinter qualified as PP
import SF2TAL.F.F
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Plate
import SF2TAL.Uniq
import SF2TAL.Utils


type TcEnv = M.Map Name Ty


type TcSt = M.Map TName Ty


data TcException where
  TcException ::
    HasCallStack =>
    { msg :: PP.Doc ann
    , env :: TcEnv
    , st :: TcSt
    } ->
    TcException


instance Show TcException where
  show (TcException{msg, env, st}) =
    docStr $
      PP.vsep
        [ msg
        , "env:"
        , ppMap ":" env
        , "substitutions:"
        , ppMap ":" st
        , pp $ prettyCallStack callStack
        ]


instance Exception TcException


type Tc es = (Uniq :> es, Reader TcEnv :> es, State TcSt :> es)


err :: (HasCallStack, Tc es) => PP.Doc ann -> Eff es a
err msg = do
  env <- ask
  st <- get
  throwM $ TcException{msg, env, st}


extendEnv :: Tc es => Name -> Ty -> Eff es a -> Eff es a
extendEnv x t = local (M.insert x t)


type Sigma = Ty


type Rho = Ty -- No top-level forall


type Tau = Ty -- No forall anywhere


freshTName :: Uniq :> es => Eff es TName
freshTName = int2Text <$> fresh


freshMeta :: Uniq :> es => Eff es Ty
freshMeta = TVar . ("_" <>) <$> freshTName


readMeta :: Tc es => TName -> Eff es (Maybe Ty)
readMeta a = preuse (ix a)


writeMeta :: Tc es => TName -> Ty -> Eff es ()
writeMeta a t = at a .= Just t


metaTvs :: (Tc es, Traversable f) => f Ty -> Eff es (S.Set TName)
metaTvs ts = do
  ts' <- fold <$> traverse (fmap ftv . zonk) ts
  pure $ S.filter (T.isPrefixOf "_") ts'


ftvs :: Tc es => [Ty] -> Eff es (S.Set TName)
ftvs ts = do
  ts' <- fold <$> traverse (fmap ftv . zonk) ts
  pure $ S.filter (not . T.isPrefixOf "_") ts'


-- Type scheme
data Scheme = Scheme (S.Set TName) Rho


-- pr: weak prenex form conversion
skolemise :: Tc es => Sigma -> Eff es (Scheme, Tm -> Tm)
skolemise = \case
  TForall a t -> do
    -- PRPOLY
    a' <- freshTName
    (Scheme as t', f) <- skolemise $ tsubst a (TVar a') t
    pure (Scheme (S.insert a' as) t', \x -> AbsT a' $ f (x `AppT` TVar a'))
  t1 `TFun` t2 -> do
    -- PRFUN
    (Scheme as t2', f) <- skolemise t2
    y <- freshName
    pure
      ( Scheme as (t1 `TFun` t2')
      , \x ->
          Abs y (Just t1) $
            f $
              foldr AbsT (foldl (\e a -> e `AppT` TVar a) x as `App` Var y (Just t1)) as
      )
  t -> pure (Scheme mempty t, id) -- PRMONO


zonk :: (Tc es, ProjOf Plate a) => a -> Eff es a
zonk = traverseMFor $ postMap purePlate{pTy}
  where
    pTy = \case
      TVar a
        | T.isPrefixOf "_" a -> do
            readMeta a >>= \case
              Nothing -> pure $ TVar a
              Just t -> do
                t' <- zonk t
                writeMeta a t'
                pure t'
        | otherwise -> pure $ TVar a
      t -> pure t


instantiate :: Tc es => Sigma -> Eff es (Rho, Tm -> Tm)
instantiate = \case
  TForall a t -> do
    a' <- freshMeta
    pure (tsubst a a' t, (`AppT` a'))
  t -> do
    (Scheme as t', f) <- skolemise t
    pure (foldr TForall t' as, f)


quantify :: Tc es => S.Set TName -> Tm -> Ty -> Eff es (Sigma, Tm)
quantify as e t = do
  as' <- replicateM (length as) freshTName
  traverse_ (\(a, a') -> writeMeta a (TVar a')) (S.toList as `zip` as')
  t' <- zonk t
  pure (foldr TForall t' as', foldr AbsT e as')


unify :: Tc es => Tau -> Tau -> Eff es ()
unify s t = case (s, t) of
  (TVar a, TVar b)
    | a == b -> pure ()
  (TVar a, t2) | T.isPrefixOf "_" a -> unifyVar a t2
  (t1, TVar b) | T.isPrefixOf "_" b -> unifyVar b t1
  (TInt, TInt) -> pure ()
  (TFun s1 s2, TFun t1 t2) -> unify s1 t1 >> unify s2 t2
  (TTuple ss, TTuple ts) -> traverse_ (uncurry unify) (zip ss ts)
  _ -> err $ "Cannot unify" <+> pp s <+> "with" <+> pp t
  where
    unifyVar :: Tc es => TName -> Tau -> Eff es ()
    unifyVar a1 t2 =
      preuse (ix a1) >>= \case
        Just t1 -> unify t1 t2
        Nothing -> unifyUbVar a1 t2

    unifyUbVar :: Tc es => TName -> Tau -> Eff es ()
    unifyUbVar a1 t2@(TVar b1) | T.isPrefixOf "_" b1 = do
      preuse (ix b1) >>= \case
        Just t2' -> unify (TVar a1) t2'
        Nothing -> writeMeta a1 t2
    unifyUbVar a1 t2 = do
      tvs2 <- metaTvs [t2]
      if a1 `S.member` tvs2
        then err $ "Occurs check error:" <+> pp a1 <+> pp t2
        else writeMeta a1 t2


unifyFun :: Tc es => Rho -> Eff es (Rho, Rho)
unifyFun (t1 `TFun` t2) = pure (t1, t2)
unifyFun t = do
  t1 <- freshMeta
  t2 <- freshMeta
  unify t (t1 `TFun` t2)
    `catch` \(_ :: TcException) -> err ("Non-function type" <+> pp t)
  pure (t1, t2)


-- ⊢dsk
-- DEEP-SKOL: Deep skolemise
subsCheck :: Tc es => Sigma -> Sigma -> Eff es (Tm -> Tm)
subsCheck sigma1 sigma2 = do
  (Scheme as rho2, f1) <- skolemise sigma2
  f2 <- subsCheckRho sigma1 rho2
  esc <- ftvs [sigma1, sigma2]
  let bads = esc `S.union` as
  unless (null bads) do
    err $
      PP.vcat
        [ "Subsumption check failed:"
        , nest (pp sigma1)
        , "is not as polymorphic as"
        , nest (pp sigma2)
        ]
  pure \x -> f1 $ foldr AbsT (f2 x) as


-- ⊢dsk*
subsCheckRho :: Tc es => Sigma -> Rho -> Eff es (Tm -> Tm)
subsCheckRho = subsCheckRho'
  where
    subsCheckRho' :: Tc es => Sigma -> Rho -> Eff es (Tm -> Tm)
    subsCheckRho' = curry \case
      (t1@TForall{}, t2) -> do
        -- SPEC
        (t1', f1) <- instantiate t1
        f2 <- subsCheckRho t1' t2
        pure $ f2 . f1
      (t, t1' `TFun` t2') -> do
        -- FUN
        (t1, t2) <- unifyFun t
        subsCheckFun t1 t2 t1' t2'
      (t1 `TFun` t2, t) -> do
        (t1', t2') <- unifyFun t
        subsCheckFun t1 t2 t1' t2'
      (t1, t2) -> do
        -- MONO
        unify t1 t2
        pure id

    subsCheckFun :: Tc es => Sigma -> Rho -> Sigma -> Rho -> Eff es (Tm -> Tm)
    subsCheckFun t1 t2 t1' t2' = do
      f1 <- subsCheck t1' t1
      f2 <- subsCheckRho' t2 t2'
      y <- freshName
      pure \x -> Abs y (Just t1) $ f2 (x `App` f1 (Var y (Just t1)))


-- ⊢inst⇑
inferInstSigma :: Tc es => Sigma -> Eff es (Rho, Tm -> Tm)
inferInstSigma = instantiate


-- ⊢inst⇓
checkInstSigma :: Tc es => Sigma -> Rho -> Eff es (Tm -> Tm)
checkInstSigma = subsCheckRho


inferRho :: Tc es => Tm -> Eff es (Ty, Tm)
inferRho = \case
  Var x _ ->
    preview (ix x) >>= \case
      Just t -> do
        (t', f) <- inferInstSigma t
        pure (t', f $ Var x (Just t'))
      Nothing -> err $ "Unbound variable" <+> pp x
  IntLit i -> pure (TInt, IntLit i)
  LetRec xs e -> do
    ts <- traverse (const freshMeta) xs
    local (ts <>) do
      xs' <- M.traverseWithKey (\x e' -> checkSigma e' (ts M.! x)) xs
      (t, e') <- inferRho e
      pure (t, LetRec xs' e')
  Abs x1 t e -> do
    t1 <- maybe freshMeta pure t
    (t', e') <- extendEnv x1 t1 do inferRho e
    pure (t1 `TFun` t', Abs x1 (Just t1) e')
  e1 `App` e2 -> do
    (t, e1') <- inferRho e1
    (t1, t2) <- unifyFun t
    e2' <- checkSigma e2 t1
    (t2', f) <- inferInstSigma t2
    pure (t2', f $ e1' `App` e2')
  AbsT{} -> err "Explicit type abstraction"
  AppT{} -> err "Explicit type application"
  Tuple es -> do
    (ts, es') <- unzip <$> traverse inferRho es
    pure (TTuple ts, Tuple es')
  At i e -> do
    (t, e') <- inferRho e
    t' <- zonk t -- Cannot unify since we don't know the length of the tuple.
    case t' of
      TTuple ts ->
        if
          | Just t'' <- ts ^? ix (i - 1) -> pure (t'', At i e')
          | otherwise -> err "Indexing out of range"
      _ -> err $ "Indexing non tuple value" <+> pp t
  Arith p e1 e2 -> do
    e1' <- checkRho e1 TInt
    e2' <- checkRho e2 TInt
    pure (TInt, Arith p e1' e2')
  If0 v e1 e2 -> do
    v' <- checkRho v TInt
    t <- freshMeta
    e1' <- checkRho e1 t
    e2' <- checkRho e2 t
    pure (t, If0 v' e1' e2')
  e `Ann` t -> do
    e' <- checkSigma e t
    (t', f) <- inferInstSigma t
    pure (t', f e')


checkRho :: Tc es => Tm -> Ty -> Eff es Tm
checkRho e tExpect = case e of
  Abs x _t e' -> do
    (t1, t2) <- unifyFun tExpect
    local (at x ?~ t1) do Abs x (Just t1) <$> checkRho e' t2
  _ -> do
    (actual, e') <- inferRho e
    f <- checkInstSigma actual tExpect
    pure $ f e'


-- ⊢poly⇑
inferSigma :: Tc es => Tm -> Eff es (Sigma, Tm)
inferSigma e = do
  -- GEN1
  (t, e') <- inferRho e
  ts <- metaTvs [t]
  envs <- metaTvs =<< ask
  quantify (ts S.\\ envs) e' t


-- ⊢poly⇓
checkSigma :: Tc es => Tm -> Sigma -> Eff es Tm
checkSigma e t = do
  -- GEN2
  (Scheme as t', f) <- skolemise t
  e' <- checkRho e t'
  envs <- asks M.elems
  esc <- ftvs (t : envs)
  let bads = esc `S.union` as
  unless (null bads) do err "Not polymorphic enough"
  pure $ f $ foldr AbsT e' as


infer :: Uniq :> es => Tm -> Eff es Tm
infer e = runReader mempty $ evalState mempty do
  (_t, e') <- inferRho e
  zonk e'
