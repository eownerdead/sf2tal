module SF2TAL.Uniq
  ( Uniq
  , runUniq
  , fresh
  )
where

import Effectful
import Effectful.Dispatch.Static


data Uniq :: Effect


type instance DispatchOf Uniq = Static NoSideEffects


newtype instance StaticRep Uniq = Uniq Int


runUniq :: Eff (Uniq : es) a -> Eff es a
runUniq = evalStaticRep (Uniq 0)


fresh :: Uniq :> es => Eff es Int
fresh = stateStaticRep $ \(Uniq i) -> (i, Uniq $ i + 1)
