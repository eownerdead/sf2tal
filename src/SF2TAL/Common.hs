module SF2TAL.Common where

import Control.Monad.State
import Data.Text qualified as T


type TName = T.Text


type Name = T.Text


class Monad m => MonadUniq m where
  freshName :: m Name


type UniqT = StateT Int


instance Monad m => MonadUniq (UniqT m) where
  freshName = do
    n <- get
    modify (+ 1)
    pure $ T.pack $ "_" <> show n


runUniqT :: Monad m => UniqT m a -> m a
runUniqT m = evalStateT m 0
