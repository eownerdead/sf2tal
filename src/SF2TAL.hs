module SF2TAL where

import Effectful
import SF2TAL.F qualified as F
import SF2TAL.Middle qualified as M
import SF2TAL.Middle.Opt qualified as M
import SF2TAL.Tal qualified as Tal
import SF2TAL.Uniq


iter :: Uniq :> es => Int -> M.Tm -> Eff es M.Tm
iter n k
  | n == 0 = pure k
  | otherwise = do
      k' <- M.simp k
      M.ckTm k'
      iter (n - 1) k'


compile :: Uniq :> es => F.Tm -> Eff es (Tal.Prog, Tal.THeap)
compile e = do
  e' <- F.ty e
  k <- M.kProg e'
  M.ckTm k

  k' <- iter 25 k

  c <- M.cProg k'
  M.ckProg c

  a <- M.aProg c
  M.ckProg a

  (tal, ths) <- Tal.tProg a
  Tal.ckProg ths tal
  pure (tal, ths)


run :: F.Tm -> Tal.Val
run e = runPureEff $ runUniq do
  (tal, ths) <- compile e
  Tal.exec ths tal
