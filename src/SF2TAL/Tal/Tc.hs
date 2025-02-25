module SF2TAL.Tal.Tc (ckProg) where

import Control.Exception.Safe
import Control.Monad
import Data.Foldable
import Effectful
import Effectful.Reader.Static
import Effectful.Reader.Static.Microlens
import GHC.Stack
import Lens.Micro.Platform hiding (preview, view)
import Prettyprinter qualified as PP
import SF2TAL.PP
import SF2TAL.Tal.Tal
import SF2TAL.Utils


data TcEnv = TcEnv
  { tHeap :: THeap
  , tRegFile :: TRegFile
  }


makeFieldsId ''TcEnv


data TcException where
  TcException :: HasCallStack => PP.Doc ann -> THeap -> TRegFile -> TcException


instance Show TcException where
  show (TcException e th trf) =
    docStr $
      PP.vsep
        [ e
        , "heap types:"
        , ppMap ":" th
        , "register file types:"
        , ppMap ":" trf
        , pp $ prettyCallStack callStack
        ]


instance Exception TcException


type Tc ann es = (Reader TcEnv :> es)


err :: (HasCallStack, Tc ann es) => [PP.Doc ann] -> Eff es a
err es = do
  th <- view tHeap
  trf <- view tRegFile
  throwM $ TcException (PP.vsep es) th trf


ckProg :: THeap -> Prog -> Eff es ()
ckProg ths p = runReader TcEnv{tHeap = ths, tRegFile = mempty} do ckProg' p


ckProg' :: Tc ann es => Prog -> Eff es ()
ckProg' (Prog h r is) = do
  ckHeaps h
  tRegFile' <- tyRegFile r
  local (tRegFile .~ tRegFile') do tySeq is


ckHeaps :: Tc ann es => Heaps -> Eff es ()
ckHeaps = traverse_ ckHeapVal


ckHeapVal :: Tc ann es => HVal -> Eff es ()
ckHeapVal = \case
  Code _as trs is -> local (tRegFile .~ trs) do tySeq is
  Tuple{} -> pure ()


tySeq :: Tc ann es => Seq -> Eff es ()
tySeq (Seq i is) = case i of
  Arith _p rd rs v -> do
    tyR rs >>= \t ->
      when (t /= TInt) do
        err ["2nd operand is not int, but" <+> pp t, pp i]
    tyVal v >>= \t ->
      when (t /= TInt) do
        err ["3rd operand is not int, but" <+> pp t]
    local (tRegFile . at rd ?~ TInt) $ tySeq is
  Bnz r v -> do
    tyR r >>= \t ->
      when (t /= TInt) do err ["1st is not int, but" <+> pp t, pp i]
    tySeq (Jmp v)
    tySeq is
  Ld rd rs k ->
    tyR rs >>= \case
      TTuple ts ->
        if
          | Just (t, True) <- ts ^? ix k ->
              local (tRegFile . at rd ?~ t) do tySeq is
          | otherwise -> err ["ld out of range", pp i]
      t -> err ["2nd operand is not tuple, but" <+> pp t, pp i]
  Malloc rd ts ->
    local (tRegFile . at rd ?~ TTuple (fmap (,False) ts)) do tySeq is
  Mov rd v -> do
    t <- tyVal v
    local (tRegFile . at rd ?~ t) do tySeq is
  St rd k rs ->
    tyR rd >>= \case
      TTuple ts ->
        if
          | Just (t, _) <- ts ^? ix k -> do
              t' <- tyR rs
              when (t' /= t) do
                err
                  [ "Type of st does not match"
                  , "expected:" <+> pp t
                  , "actual:" <+> pp t'
                  , pp i
                  ]
              local (tRegFile . at rd ?~ TTuple (ts & ix k . _2 .~ True)) do tySeq is
          | otherwise -> err ["st out of range", pp i]
      t -> err ["1st operand is not tuple, but" <+> pp t, pp i]
  Unpack a rd v ->
    tyVal v >>= \case
      TExists b t ->
        local (tRegFile . at rd ?~ tsubst b (TVar a) t) do tySeq is
      t -> err ["Unpacking non-existential value: " <+> pp t, pp i]
tySeq (Jmp v) = do
  trs <- view tRegFile
  tyVal v >>= \case
    TCode [] trs' ->
      unless (trs `isSubtyOf` trs') do
        err ["Register file is not subtype", pp $ Jmp v]
    t ->
      err ["Operand must be code" <+> pp t, pp $ Jmp v]
tySeq (Halt t) = do
  t' <- preview (tRegFile . ix (A 1))
  when (t' /= Just t) do
    err ["Type of operand does not match with" <+> pp t', pp $ Halt t]


tyR :: Tc ann es => R -> Eff es Ty
tyR r =
  preview (tRegFile . ix r) >>= \case
    Just t -> pure t
    _ -> err ["Undefined register " <> pp r]


tyRegFile :: Tc ann es => RegFile -> Eff es TRegFile
tyRegFile = traverse tyWVal


tyWVal :: Tc ann es => Val -> Eff es Ty
tyWVal = \case
  Label l ->
    preview (tHeap . ix l) >>= \case
      Just t -> pure t
      _ -> err ["Undefined label " <> pp l]
  IntLit _ -> pure TInt
  Junk t -> pure t
  AppT w t ->
    tyWVal w >>= \case
      TCode [] trs -> pure $ TCode [] trs
      TCode (a : as) trs -> pure $ TCode as $ tsubst a t trs
      t' -> err ["Type applying non-code value: " <> pp t', pp $ AppT w t]
  Pack _t w t' -> do
    _ <- tyWVal w
    pure t'
  w -> err ["Not a word value: " <> pp w]


tyVal :: Tc ann es => Val -> Eff es Ty
tyVal = \case
  Reg r -> tyR r
  AppT v t ->
    tyVal v >>= \case
      TCode [] trs -> pure $ TCode [] trs
      TCode (a : as) trs -> pure $ TCode as $ tsubst a t trs
      t' -> err ["Type applying non-code value: " <> pp t', pp $ AppT v t]
  Pack _t v t' -> do
    _ <- tyVal v
    pure t'
  x -> tyWVal x
