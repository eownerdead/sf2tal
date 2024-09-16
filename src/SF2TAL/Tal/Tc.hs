module SF2TAL.Tal.Tc (ckProg) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Foldable
import Data.Text qualified as T
import Lens.Micro.Platform
import Prettyprinter qualified as PP
import SF2TAL.Common
import SF2TAL.Tal.Tal


data TcEnv = TcEnv {tcEnvTHeap :: THeap, tcEnvTRegFile :: TRegFile}


makeFields ''TcEnv


type Tc = ReaderT TcEnv (Either T.Text)


ckProg :: THeap -> Prog -> Either T.Text ()
ckProg ths p =
  runReaderT
    (ckProg' p)
    (TcEnv{tcEnvTHeap = ths, tcEnvTRegFile = mempty})


ckProg' :: Prog -> Tc ()
ckProg' (Prog h r is) = do
  ckHeaps h
  tRegFile' <- tyRegFile r
  local (tRegFile .~ tRegFile') $ tySeq is


ckHeaps :: Heaps -> Tc ()
ckHeaps = traverse_ ckHeapVal


ckHeapVal :: HVal -> Tc ()
ckHeapVal (Code _as trs is) = local (tRegFile .~ trs) $ tySeq is
ckHeapVal Tuple{} = pure ()


tySeq :: Seq -> Tc ()
tySeq (Seq i is) = case i of
  Arith _op rd rs v -> do
    tyR rs >>= \t ->
      when (t /= TInt) $
        throwError $
          "Arith: rs is not Int, but " <> prettyText t
    tyVal v >>= \t ->
      when (t /= TInt) $
        throwError $
          "Arith: v is not Int, but " <> prettyText t
    local (tRegFile . at rd ?~ TInt) $ tySeq is
  Bnz r v -> do
    tyR r >>= \t ->
      when (t /= TInt) $ throwError $ "Bnz: r is not Int, but " <> prettyText t
    tySeq (Jmp v)
    tySeq is
  Ld rd rs k ->
    tyR rs >>= \case
      TTuple ts
        | Just (t, True) <- ts ^? ix k ->
            local (tRegFile . at rd ?~ t) $ tySeq is
      _ -> throwError "Ld: rs is not TTuple or i is invalid"
  Malloc rd ts ->
    local (tRegFile . at rd ?~ TTuple (fmap (,False) ts)) $ tySeq is
  Mov rd v -> do
    t <- tyVal v
    local (tRegFile . at rd ?~ t) $ tySeq is
  St rd k rs ->
    tyR rd >>= \case
      TTuple ts | Just (t, _) <- ts ^? ix k -> do
        tyR rs >>= \t' ->
          when (t' /= t) $
            throwError $
              "St: rs is not ts[i], but " <> prettyText t'
        local (tRegFile . at rd ?~ TTuple (ts & ix k . _2 .~ True)) $ tySeq is
      t -> throwError $ "St: rd is not TTuple, but " <> prettyText t
  Unpack a rd v ->
    tyVal v >>= \case
      TExists b t ->
        local (tRegFile . at rd ?~ tsubst b (TVar a) t) $ tySeq is
      t -> throwError $ "Unpack: v is not TExists, but " <> prettyText t
tySeq (Jmp v) = do
  trs <- view tRegFile
  tyVal v >>= \case
    TCode [] trs' ->
      unless (trs `isSubtyOf` trs') $
        throwError $
          "Jmp: register file is not subtype of "
            <> prettyText v
            <> T.pack (show (prettyMap PP.colon trs))
            <> T.pack (show (prettyMap PP.colon trs'))
    t ->
      throwError $ "Jmp: v is not TCode, but " <> prettyText t <> prettyText v
tySeq (Halt t) =
  preview (tRegFile . ix "1") >>= \t' ->
    when (t' /= Just t) $
      throwError $
        "Halt: r1 is not t, but " <> prettyText t'


tyR :: R -> Tc Ty
tyR r =
  preview (tRegFile . ix r) >>= \case
    Just t -> pure t
    _ -> throwError $ "R: undefined register " <> prettyText r


tyRegFile :: RegFile -> Tc TRegFile
tyRegFile = traverse tyWVal


tyWVal :: Val -> Tc Ty
tyWVal (Label l) =
  preview (tHeap . ix l) >>= \case
    Just t -> pure t
    _ -> throwError $ "Label: undefined label " <> prettyText l
tyWVal (IntLit _) = pure TInt
tyWVal (Junk t) = pure t
tyWVal (AppT w t) =
  tyWVal w >>= \case
    TCode [] trs -> pure $ TCode [] trs
    TCode (a : as) trs -> pure $ TCode as $ tsubst a t trs
    t' -> throwError $ "AppT: w is not TCode, but " <> prettyText t'
tyWVal (Pack _t w t') = do
  _ <- tyWVal w
  pure t'
tyWVal w = throwError $ "not word value: " <> prettyText w


tyVal :: Val -> Tc Ty
tyVal (Reg r) = tyR r
tyVal (Pack _t w t') = do
  _ <- tyVal w
  pure t'
tyVal x = tyWVal x
