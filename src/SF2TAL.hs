module SF2TAL where

import Data.Text qualified as T
import Data.Text.IO qualified as T
import Effectful
import SF2TAL.F qualified as F
import SF2TAL.Middle qualified as M
import SF2TAL.Middle.Opt qualified as M
import SF2TAL.PP
import SF2TAL.Tal qualified as Tal
import SF2TAL.Uniq


iter :: Uniq :> es => Int -> M.Tm -> Eff es M.Tm
iter n k
  | n == 0 = pure k
  | otherwise = do
      k' <- M.simp k
      M.ckTm k'
      iter (n - 1) k'


compile :: Uniq :> es => T.Text -> Eff es (Tal.Prog, Tal.THeap)
compile s = do
  e <- F.parse s
  e' <- F.infer e
  F.ck e'

  k <- M.kProg e'
  M.ckTm k

  k' <- iter 5 k

  c <- M.cProg k'
  M.ckTm c

  a <- M.aProg c
  M.ckTm a

  (tal, ths) <- Tal.tProg a
  Tal.ckProg ths tal
  pure (tal, ths)


run :: T.Text -> Eff es Tal.Val
run s = runUniq do
  (tal, ths) <- compile s
  Tal.exec ths tal


main :: IO ()
main = runEff $ runUniq do
  liftIO . T.putStrLn . docText . pp =<< run =<< liftIO T.getContents
