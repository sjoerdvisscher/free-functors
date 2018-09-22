{-# LANGUAGE
    GADTs
  , RankNTypes
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , MultiParamTypeClasses
  , QuantifiedConstraints
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.HHCofree
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A cofree functor is right adjoint to a forgetful functor.
-- In this package the forgetful functor forgets class constraints.
--
-- Compared to @Data.Functor.HCofree@ we have 2 two parameters.
-----------------------------------------------------------------------------
module Data.Functor.HHCofree where

import Prelude hiding ((.), id)

import Control.Category
import Data.Bifunctor
import Data.Bifunctor.Functor
import Data.Profunctor
import Data.Profunctor.Unsafe
import Data.Profunctor.Monad


-- | Natural transformations.
type f :~~> g = forall c d. f c d -> g c d

-- | The higher order cofree functor for constraint @c@.
data HHCofree c g a b where
  HHCofree :: c f => (f :~~> g) -> f a b -> HHCofree c g a b


counit :: HHCofree c g :~~> g
counit (HHCofree k fa) = k fa

leftAdjunct :: c f => (f :~~> g) -> f :~~> HHCofree c g
leftAdjunct k fa = HHCofree k fa

-- | @unit = leftAdjunct id@
unit :: c g => g :~~> HHCofree c g
unit = leftAdjunct id

-- | @rightAdjunct f = counit . f@
rightAdjunct :: (f :~~> HHCofree c g) -> f :~~> g
rightAdjunct f = counit . f

transform :: (forall r. c r => (r :~~> f) -> r :~~> g) -> HHCofree c f :~~> HHCofree c g
transform t (HHCofree k a) = HHCofree (t k) a

hfmap :: (f :~~> g) -> HHCofree c f :~~> HHCofree c g
hfmap f = transform (\k -> f . k)

hextend :: (HHCofree c f :~~> g) -> HHCofree c f :~~> HHCofree c g
hextend f = transform (\k -> f . leftAdjunct k)


instance BifunctorFunctor (HHCofree c) where
  bifmap = hfmap

instance BifunctorComonad (HHCofree c) where
  biextract = counit
  biextend = hextend
  
instance ProfunctorFunctor (HHCofree c) where
  promap = hfmap

instance ProfunctorComonad (HHCofree c) where
  proextract = counit
  produplicate = hextend id


instance (forall x. c x => Bifunctor x) => Bifunctor (HHCofree c g) where
  bimap f g (HHCofree k a) = HHCofree k (bimap f g a)
  first f (HHCofree k a) = HHCofree k (first f a)
  second f (HHCofree k a) = HHCofree k (second f a)
      
instance (forall x. c x => Profunctor x) => Profunctor (HHCofree c g) where
  dimap f g (HHCofree k a) = HHCofree k (dimap f g a)
  lmap f (HHCofree k a) = HHCofree k (lmap f a)
  rmap f (HHCofree k a) = HHCofree k (rmap f a)
  f #. HHCofree k g = HHCofree k (f #. g)
  HHCofree k g .# f = HHCofree k (g .# f)
      
instance (forall x. c x => Strong x) => Strong (HHCofree c f) where
  first' (HHCofree k a) = HHCofree k (first' a)
  second' (HHCofree k a) = HHCofree k (second' a)
      
instance (forall x. c x => Choice x) => Choice (HHCofree c f) where
  left' (HHCofree k a) = HHCofree k (left' a)
  right' (HHCofree k a) = HHCofree k (right' a)
      
instance (forall x. c x => Closed x) => Closed (HHCofree c f) where
  closed (HHCofree k a) = HHCofree k (closed a)
