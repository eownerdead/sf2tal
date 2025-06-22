module SF2TAL.Name
  ( Name (..)
  , freshName
  )
where

import Data.Text qualified as T
import Effectful
import Prettyprinter qualified as PP
import SF2TAL.PP
import SF2TAL.Uniq


data Name = Name {name :: T.Text, uniq :: Int}


deriving stock instance Eq Name


deriving stock instance Ord Name


deriving stock instance Show Name


instance PP.Pretty Name where
  pretty Name{name, uniq} = pp name <> "." <> pp uniq


freshName :: Uniq :> es => Eff es Name
freshName = Name "" <$> fresh
