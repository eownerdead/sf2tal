module SF2TAL.Log
  ( LogLevel (..)
  , showLogLevel
  , Log (..)
  , logMsg
  , runLogHandle
  , runLogStderr
  )
where

import Data.Ix
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.TH
import System.IO


data LogLevel = Debug | Info
  deriving stock (Eq, Ord, Ix, Enum, Bounded)


showLogLevel :: LogLevel -> T.Text
showLogLevel = \case
  Debug -> "debug: "
  Info -> "info:  "


data Log :: Effect where
  LogMsg :: HasCallStack => LogLevel -> T.Text -> Log m ()


$(makeEffect ''Log)


runLogHandle ::
  IOE :> es => Handle -> (LogLevel -> Bool) -> Eff (Log : es) a -> Eff es a
runLogHandle h f = interpret \_ -> \case
  LogMsg level msg
    | f level -> liftIO $ T.hPutStrLn h (showLogLevel level <> msg)
    | otherwise -> pure ()


runLogStderr :: IOE :> es => (LogLevel -> Bool) -> Eff (Log : es) a -> Eff es a
runLogStderr = runLogHandle stderr
