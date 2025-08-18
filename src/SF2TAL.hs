module SF2TAL where

import Data.ByteString.Lazy.Char8 qualified as C
import Data.Text qualified as T
import Data.Text.Foreign qualified as T
import Data.Text.IO qualified as T
import Effectful
import Foreign.C.String
import Foreign.Ptr
import LLVM.FFI.Analysis qualified as L
import LLVM.FFI.BitWriter qualified as L
import LLVM.FFI.Core qualified as L
import Lens.Micro.Platform
import SF2TAL.F qualified as F
import SF2TAL.Llvm qualified as L
import SF2TAL.Middle qualified as M
import SF2TAL.PP
import SF2TAL.Uniq
import SF2TAL.Utils
import System.Process.Typed qualified as P
import UnliftIO


compile :: (IOE :> es, Uniq :> es, Log :> es) => T.Text -> Eff es L.ModuleRef
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

  logMsg Info "Converting to lambda C"
  c <- M.cProg k
  logMsg Debug $ docText $ pp c
  logMsg Info "Verifying lambda C"
  M.ckTm c

  logMsg Info "Converting to lambda A"
  a <- M.aProg c
  logMsg Debug $ docText $ pp a
  logMsg Info "Verifying to lambda A"
  M.ckTm a

  logMsg Info "Converting to LLVM IR"
  m <- L.lProg a
  liftIO $ L.dumpModule m
  logMsg Info "Verifying LLVM IR"
  _ <- liftIO $ L.verifyModule m 1 nullPtr
  pure m


run :: (IOE :> es, Log :> es) => T.Text -> Eff es Int
run s = runUniq do
  m <- compile s
  logMsg Info "Compiling LLVM IR"
  withSystemTempDirectory "sf2tal" \path -> do
    _ <- liftIO $ withCString (path <> "/run.bc") $ L.writeBitcodeToFile m
    P.runProcess_ do
      P.shell $ "clang -o " <> path <> "/run " <> path <> "/run.bc rt/rt.c"
    logMsg Info "Executing"
    r <- P.readProcessStdout_ do P.shell $ path <> "/run"
    case C.readInt r of
      Just (i, _) -> pure i
      Nothing -> error "Cannot read the output"


main :: IO ()
main = runEff $ runLogStderr (const True) $ runUniq do
  m <- compile =<< liftIO T.getContents
  _ <- liftIO $ T.withCString "main.bc" $ L.writeBitcodeToFile m
  pure ()
