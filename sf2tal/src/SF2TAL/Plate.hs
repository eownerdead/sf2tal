-- https://arxiv.org/abs/1103.2841v2
-- https://hackage.haskell.org/package/multiplate-0.0.3
-- https://hackage.haskell.org/package/multiplate-simplified-0.0.0.2

module SF2TAL.Plate
  ( module Data.Functor.Const
  , module Data.Functor.Identity
  , Proj
  , Multiplate (..)
  , ProjOf (..)
  , purePlate
  , kleisliComposePlate
  , appendPlate
  , traverseMFor
  , traverseFor
  , foldFor
  , preMap
  , postMap
  , preFold
  , postFold
  )
where

import Control.Monad
import Data.Functor.Const
import Data.Functor.Identity
import Prelude


type Proj p a = forall f. p f -> a -> f a


class Multiplate p where
  multiplate :: Applicative f => p f -> p f
  mkPlate :: (forall a. Proj p a -> a -> f a) -> p f


class Multiplate p => ProjOf p a where
  getProj :: Proj p a


purePlate :: (Multiplate p, Applicative f) => p f
purePlate = mkPlate \_ -> pure {- HLINT ignore -}


kleisliComposePlate :: (Multiplate p, Monad m) => p m -> p m -> p m
kleisliComposePlate f1 f2 = mkPlate \proj -> proj f1 <=< proj f2


appendPlate ::
  (Multiplate p, Monoid o) => p (Const o) -> p (Const o) -> p (Const o)
appendPlate f1 f2 = mkPlate \proj a -> proj f1 a <* proj f2 a


traverseMFor :: ProjOf p a => p f -> a -> f a
traverseMFor f a = getProj f a


traverseFor :: ProjOf p a => p Identity -> a -> a
traverseFor f a = runIdentity $ traverseMFor f a


foldFor :: ProjOf p a => p (Const o) -> a -> o
foldFor f a = getConst $ traverseMFor f a


preMap :: (Multiplate p, Monad m) => p m -> p m
preMap f = multiplate (preMap f) `kleisliComposePlate` f


postMap :: (Multiplate p, Monad m) => p m -> p m
postMap f = f `kleisliComposePlate` multiplate (postMap f)


preFold :: (Multiplate p, Monoid o) => p (Const o) -> p (Const o)
preFold f = f `appendPlate` multiplate (preFold f)


postFold :: (Multiplate p, Monoid o) => p (Const o) -> p (Const o)
postFold f = multiplate (postFold f) `appendPlate` f
