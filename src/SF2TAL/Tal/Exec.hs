module SF2TAL.Tal.Exec
  ( ExecEnv (..)
  , HasHeaps (..)
  , HasTHeap (..)
  , HasRegFile (..)
  , Exec
  , getProg
  , exec
  , step
  )
where

import Data.Text qualified as T
import Effectful
import Effectful.Error.Static
import Effectful.State.Static.Local
import Effectful.State.Static.Local.Microlens
import Lens.Micro.Platform hiding (preuse, use, (%=), (?=))
import SF2TAL.F (Prim (..))
import SF2TAL.Tal.Tal
import SF2TAL.Tal.Tc
import SF2TAL.Uniq
import SF2TAL.Utils


data ExecEnv = ExecEnv
  { heaps :: Heaps
  , tHeap :: THeap
  , regFile :: RegFile
  }


makeFieldsId ''ExecEnv


type Exec es = (Uniq :> es, State ExecEnv :> es)


getProg :: Exec es => Seq -> Eff es Prog
getProg is = do
  hs <- use heaps
  rs <- use regFile
  pure $ Prog hs rs is


exec :: (Uniq :> es, Error T.Text :> es) => THeap -> Prog -> Eff es Val
exec ths (Prog hs rs is) = do
  (_, env) <-
    runState ExecEnv{heaps = hs, tHeap = ths, regFile = rs} do
      exec' is
  pure $ env ^. regFile ^?! ix (A 1)
  where
    exec' :: (Exec es, Error T.Text :> es) => Seq -> Eff es Seq
    exec' (Halt t) = pure $ Halt t
    exec' is' = do
      p <- getProg is'
      ths' <- use tHeap
      ckProg ths' p
      exec' =<< step is'


step :: Exec es => Seq -> Eff es Seq
step (Seq i is) = case i of
  Arith p rd rs v -> do
    rs' <- reg rs
    v' <- val v
    case (rs', v') of
      (IntLit irs, IntLit iv) ->
        let k = case p of
              Add -> irs + iv
              Mul -> irs * iv
              Sub -> irs - iv
        in regFile . at rd ?= IntLit k
      _ -> error "Arith: rs or v is not IntLit"
    pure is
  Bnz r v -> do
    reg r >>= \vr ->
      if vr == IntLit 0
        then pure is
        else step (Jmp v)
  Ld rd rs k -> do
    reg rs >>= \case
      Label l ->
        heap l >>= \case
          Tuple ws ->
            if
              | Just w <- ws ^? ix k -> do
                  regFile . at rd ?= w
                  pure is
              | otherwise -> error $ "Ld: invalid index " <> show k
          _ -> error $ "Ld: " <> T.unpack (prettyText l) <> " is not Tuple"
      _ -> error "Ld: rs is not label"
  Malloc rd ts -> do
    l <- fresh
    heaps . at l ?= Tuple (fmap Junk ts)
    tHeap . at l ?= TTuple (fmap (,False) ts)
    regFile . at rd ?= Label l
    pure is
  Mov rd v -> do
    v' <- val v
    regFile . at rd ?= v'
    pure is
  St rd k rs ->
    reg rd >>= \case
      Label l ->
        heap l >>= \case
          Tuple ws -> do
            vrs <- reg rs
            heaps . at l ?= Tuple (ws & ix k .~ vrs)
            tHeap . at l %= \case
              Just (TTuple ts) -> Just $ TTuple (ts & ix k . _2 .~ True)
              _ -> error "St: l in tHeap is not TTuple"
            pure is
          _ -> error $ "St: " <> T.unpack (prettyText l) <> " is not tuple"
      _ -> error "St: rd is not label"
  Unpack a rd v ->
    val v >>= \case
      Pack t w _t' -> do
        regFile . at rd ?= w
        pure $ tsubst a t is
      t -> error $ "Unpack: v is not Pack, but" <> T.unpack (prettyText t)
step (Jmp v) = val v >>= \v' -> app v' id
  where
    app (Label l) k =
      heap l >>= \case
        Code as _ is' ->
          pure $ foldr (uncurry tsubst) is' $ zip as (k [])
        t -> error $ "Jmp: l is not Code, but " <> T.unpack (prettyText t)
    app (AppT v'' t) k = app v'' \ts -> k (t : ts)
    app _ _ = error "Jmp: v is not Label"
step (Halt t) = pure $ Halt t


heap :: Exec es => Name -> Eff es HVal
heap l =
  preuse (heaps . ix l) >>= \case
    Just v -> pure v
    _ -> error $ T.unpack $ "undefined heap label " <> prettyText l


reg :: Exec es => R -> Eff es Val
reg r =
  preuse (regFile . ix r) >>= \case
    Just v -> pure v
    _ -> error $ T.unpack $ "undefined register " <> prettyText r


val :: Exec es => Val -> Eff es Val
val = \case
  Reg r -> reg r
  AppT v t -> AppT <$> val v <*> pure t
  Pack t v t' -> Pack t <$> val v <*> pure t'
  w -> pure w
