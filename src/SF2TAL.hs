module SF2TAL where

import Data.Text qualified as T
import Data.Text.IO qualified as T
import Effectful
import Prettyprinter qualified as PP
import SF2TAL.F qualified as F
import SF2TAL.Middle qualified as M
import SF2TAL.Middle.Opt qualified as M
import SF2TAL.PP
import SF2TAL.Tal qualified as Tal
import SF2TAL.Uniq
import SF2TAL.Utils


iter :: (Uniq :> es, Log :> es) => Int -> M.Tm -> Eff es M.Tm
iter n k
  | n == 0 = pure k
  | otherwise = do
      logMsg Info $ "Optimising lambda K (" <> int2Text n <> ")"
      k' <- M.simp k
      logMsg Debug $ docText $ pp k'
      logMsg Info $ "Verifying optimising lambda K (" <> int2Text n <> ")"
      M.ckTm k'
      iter (n - 1) k'


compile :: (Uniq :> es, Log :> es) => T.Text -> Eff es (Tal.Prog, Tal.THeap)
compile s = do
  logMsg Info "Parsing"
  e <- F.parse s
  logMsg Debug $ docText $ pp e

  logMsg Info "Inferring types"
  e' <- F.infer e
  logMsg Debug $ docText $ pp e'
  logMsg Info "Verifying inferred types"
  F.ck e'

  logMsg Info "Converting to lambda K"
  k <- M.kProg e'
  logMsg Debug $ docText $ pp k
  logMsg Info "Verifying lambda K"
  M.ckTm k

  logMsg Info "Optimising lambda K"
  k' <- iter 5 k

  logMsg Info "Converting to lambda C"
  c <- M.cProg k'
  logMsg Debug $ docText $ pp c
  logMsg Info "Verifying lambda C"
  M.ckTm c

  logMsg Info "Converting to lambda A"
  a <- M.aProg c
  logMsg Debug $ docText $ pp a
  logMsg Info "Verifying to lambda A"
  M.ckTm a

  logMsg Info "Converting to TAL"
  (tal, ths) <- Tal.tProg a
  logMsg Debug $ docText $ PP.vsep [pp tal, ppMap ":" ths]
  logMsg Info "Verifying to TAL"
  Tal.ckProg ths tal
  pure (tal, ths)


run :: Log :> es => T.Text -> Eff es Tal.Val
run s = runUniq do
  (tal, ths) <- compile s
  logMsg Info "Executing TAL"
  v <- Tal.exec ths tal
  logMsg Debug $ docText $ pp v
  pure v


main :: IO ()
main = runEff $ runLogStderr (const False) do
  _ <- run =<< liftIO T.getContents
  pure ()
