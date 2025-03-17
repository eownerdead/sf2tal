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

import Control.Exception.Safe
import Effectful
import Effectful.State.Static.Local
import Effectful.State.Static.Local.Microlens
import GHC.Stack
import Lens.Micro.Platform hiding (preuse, use, (%=), (?=))
import Prettyprinter qualified as PP
import SF2TAL.F (Prim (..))
import SF2TAL.Name
import SF2TAL.PP
import SF2TAL.Tal.Tal
import SF2TAL.Uniq
import SF2TAL.Utils


data ExecEnv = ExecEnv
  { heaps :: Heaps
  , tHeap :: THeap
  , regFile :: RegFile
  }


makeFieldsId ''ExecEnv


type Exec es = (Uniq :> es, State ExecEnv :> es)


data ExecException where
  ExecException ::
    HasCallStack => PP.Doc ann -> Heaps -> THeap -> RegFile -> ExecException


instance Show ExecException where
  show (ExecException e hs th rs) =
    docStr $
      PP.vsep
        [ e
        , "heaps:"
        , ppMap "=" hs
        , "heap types:"
        , ppMap ":" th
        , "register file types:"
        , ppMap ":" rs
        , pp $ prettyCallStack callStack
        ]


instance Exception ExecException


err :: (HasCallStack, Exec es) => [PP.Doc ann] -> Eff es a
err es = do
  hs <- use heaps
  th <- use tHeap
  rs <- use regFile
  throwM $ ExecException (PP.vsep es) hs th rs


getProg :: Exec es => Seq -> Eff es Prog
getProg is = do
  hs <- use heaps
  rs <- use regFile
  pure $ Prog hs rs is


exec :: Uniq :> es => THeap -> Prog -> Eff es Val
exec ths (Prog hs rs is) = do
  (_, env) <-
    runState ExecEnv{heaps = hs, tHeap = ths, regFile = rs} do
      exec' is
  pure $ env ^. regFile ^?! ix (A 1)
  where
    exec' :: Exec es => Seq -> Eff es Seq
    exec' (Halt t) = pure $ Halt t
    exec' is' = do
      p <- getProg is'
      ths' <- use tHeap
      -- ckProg ths' p
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
      _ -> err ["Type of operands is not int", pp i]
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
              | otherwise -> err ["Invalid index" <+> pp k, pp i]
          w -> err ["Value of 2nd operand is not tuple, but" <+> pp w, pp i]
      r' -> err ["2nd operand is not label, but" <+> pp r', pp i]
  Malloc rd ts -> do
    l <- freshName
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
              _ -> error "Type of 1st operand is not tuple"
            pure is
          w -> err ["Value of 1st operand is not tuple, but" <+> pp w, pp i]
      r' -> err ["1st operand is not label, but" <+> pp r', pp i]
  Unpack a rd v ->
    val v >>= \case
      Pack t w _t' -> do
        regFile . at rd ?= w
        pure $ tsubst a t is
      t -> err ["Unpacking non-packed value: " <> pp t, pp i]
step (Jmp v) = val v >>= \v' -> app v' id
  where
    app (Label l) k =
      heap l >>= \case
        Code as _ is' ->
          pure $ foldr (uncurry tsubst) is' $ zip as (k [])
        t -> err ["Value of 1st operand is not code, but" <+> pp t, pp $ Jmp v]
    app (AppT v'' t) k = app v'' \ts -> k (t : ts)
    app v' _ =
      err
        [ "1st operand is not label or applying type:" <+> pp v'
        , pp $ Jmp v
        ]
step (Halt t) = pure $ Halt t


heap :: Exec es => Name -> Eff es HVal
heap l =
  preuse (heaps . ix l) >>= \case
    Just v -> pure v
    _ -> err ["Undefined heap label" <+> pp l]


reg :: Exec es => R -> Eff es Val
reg r =
  preuse (regFile . ix r) >>= \case
    Just v -> pure v
    _ -> err ["Undefined register" <+> pp r]


val :: Exec es => Val -> Eff es Val
val = \case
  Reg r -> reg r
  AppT v t -> AppT <$> val v <*> pure t
  Pack t v t' -> Pack t <$> val v <*> pure t'
  w -> pure w
