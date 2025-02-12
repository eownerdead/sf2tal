module SF2TAL.Tal.Tc (ckProg) where

import Control.Monad
import Data.Foldable
import Data.Text qualified as T
import Effectful
import Effectful.Error.Static
import Effectful.Reader.Static
import Effectful.Reader.Static.Microlens
import Lens.Micro.Platform hiding (preview, view)
import SF2TAL.Tal.Tal
import SF2TAL.Utils


data TcEnv = TcEnv
  { tHeap :: THeap
  , tRegFile :: TRegFile
  }


makeFieldsId ''TcEnv


type Tc es = (Reader TcEnv :> es, Error T.Text :> es)


ckProg :: Error T.Text :> es => THeap -> Prog -> Eff es ()
ckProg ths p = runReader TcEnv{tHeap = ths, tRegFile = mempty} do ckProg' p


ckProg' :: Tc es => Prog -> Eff es ()
ckProg' (Prog h r is) = do
  ckHeaps h
  tRegFile' <- tyRegFile r
  local (tRegFile .~ tRegFile') do tySeq is


ckHeaps :: Tc es => Heaps -> Eff es ()
ckHeaps = traverse_ ckHeapVal


ckHeapVal :: Tc es => HVal -> Eff es ()
ckHeapVal = \case
  Code _as trs is -> local (tRegFile .~ trs) do tySeq is
  Tuple{} -> pure ()


tySeq :: Tc es => Seq -> Eff es ()
tySeq (Seq i is) = case i of
  Arith _p rd rs v -> do
    tyR rs >>= \t ->
      when (t /= TInt) do
        throwError $
          "Arith: rs is not Int, but " <> prettyText t
    tyVal v >>= \t ->
      when (t /= TInt) do
        throwError $
          "Arith: v is not Int, but " <> prettyText t
    local (tRegFile . at rd ?~ TInt) $ tySeq is
  Bnz r v -> do
    tyR r >>= \t ->
      when (t /= TInt) do throwError $ "Bnz: r is not Int, but " <> prettyText t
    tySeq (Jmp v)
    tySeq is
  Ld rd rs k ->
    tyR rs >>= \case
      TTuple ts
        | Just (t, True) <- ts ^? ix k ->
            local (tRegFile . at rd ?~ t) do tySeq is
      _ -> throwError "Ld: rs is not TTuple or i is invalid"
  Malloc rd ts ->
    local (tRegFile . at rd ?~ TTuple (fmap (,False) ts)) do tySeq is
  Mov rd v -> do
    t <- tyVal v
    local (tRegFile . at rd ?~ t) do tySeq is
  St rd k rs ->
    tyR rd >>= \case
      TTuple ts | Just (t, _) <- ts ^? ix k -> do
        tyR rs >>= \t' ->
          when (t' /= t) do
            throwError $
              "St: rs is not ts[i], but " <> prettyText t'
        local (tRegFile . at rd ?~ TTuple (ts & ix k . _2 .~ True)) do tySeq is
      t -> throwError $ "St: rd is not TTuple, but " <> prettyText t
  Unpack a rd v ->
    tyVal v >>= \case
      TExists b t ->
        local (tRegFile . at rd ?~ tsubst b (TVar a) t) do tySeq is
      t -> throwError $ "Unpack: v is not TExists, but " <> prettyText t
tySeq (Jmp v) = do
  trs <- view tRegFile
  tyVal v >>= \case
    TCode [] trs' ->
      unless (trs `isSubtyOf` trs') do
        throwError $
          "Jmp: register file is not subtype of "
            <> prettyText v
    t ->
      throwError $ "Jmp: v is not TCode, but " <> prettyText t
tySeq (Halt t) =
  preview (tRegFile . ix (A 1)) >>= \t' ->
    when (t' /= Just t) do
      throwError $
        "Halt: r1 is not t, but " <> prettyText t'


tyR :: Tc es => R -> Eff es Ty
tyR r =
  preview (tRegFile . ix r) >>= \case
    Just t -> pure t
    _ -> throwError $ "R: undefined register " <> prettyText r


tyRegFile :: Tc es => RegFile -> Eff es TRegFile
tyRegFile = traverse tyWVal


tyWVal :: Tc es => Val -> Eff es Ty
tyWVal = \case
  Label l ->
    preview (tHeap . ix l) >>= \case
      Just t -> pure t
      _ -> throwError $ "Label: undefined label " <> prettyText l
  IntLit _ -> pure TInt
  Junk t -> pure t
  AppT w t ->
    tyWVal w >>= \case
      TCode [] trs -> pure $ TCode [] trs
      TCode (a : as) trs -> pure $ TCode as $ tsubst a t trs
      t' -> throwError $ "AppT: w is not TCode, but " <> prettyText t'
  Pack _t w t' -> do
    _ <- tyWVal w
    pure t'
  w -> throwError $ "not word value: " <> prettyText w


tyVal :: Tc es => Val -> Eff es Ty
tyVal = \case
  Reg r -> tyR r
  AppT v t ->
    tyVal v >>= \case
      TCode [] trs -> pure $ TCode [] trs
      TCode (a : as) trs -> pure $ TCode as $ tsubst a t trs
      t' -> throwError $ "AppT: w is not TCode, but " <> prettyText t'
  Pack _t w t' -> do
    _ <- tyVal w
    pure t'
  x -> tyWVal x
