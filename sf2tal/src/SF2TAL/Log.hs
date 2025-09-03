module SF2TAL.Log
  ( LogLevel (..)
  , showLogLevel
  , Log (..)
  , logMsg
  , logReport
  , logAddFile
  , runLogHandle
  , runLogStderr
  )
where

import Data.Ix
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.State.Static.Local.Microlens
import Effectful.TH
import Error.Diagnose as D
import System.IO
import Prelude


data LogLevel = Debug | Info
  deriving stock (Eq, Ord, Ix, Enum, Bounded)


showLogLevel :: LogLevel -> T.Text
showLogLevel = \case
  Debug -> "debug: "
  Info -> "info:  "


data Log :: Effect where
  LogMsg :: HasCallStack => LogLevel -> T.Text -> Log m ()
  LogReport :: D.Report T.Text -> Log m ()
  LogAddFile :: FilePath -> String -> Log m ()


$(makeEffect ''Log)


runLogHandle ::
  IOE :> es => Handle -> (LogLevel -> Bool) -> Eff (Log : es) a -> Eff es a
runLogHandle h f = reinterpret_ (evalState @(D.Diagnostic T.Text) mempty) \case
  LogMsg level msg
    | f level -> liftIO $ T.hPutStrLn h (showLogLevel level <> msg)
    | otherwise -> pure ()
  LogReport report ->
    get >>= \d ->
      D.printDiagnostic h D.WithUnicode (D.TabSize 8) D.defaultStyle $
        D.addReport d report
  LogAddFile path content -> modify \d -> D.addFile d path content


runLogStderr :: IOE :> es => (LogLevel -> Bool) -> Eff (Log : es) a -> Eff es a
runLogStderr = runLogHandle stderr
