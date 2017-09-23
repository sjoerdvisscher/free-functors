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
import Data.Constraint (Dict(..), (:-)(..))
import Data.Constraint.Class1
import Data.Functor.HHFree (HHFree(..))
import qualified Data.Functor.HHFree as F

import Control.Category
import Data.Bifunctor (Bifunctor(bimap))
import Data.Bifunctor.Functor
import Data.Profunctor
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


instance SuperClass1 Bifunctor c => Bifunctor (HHCofree c g) where
  bimap f g (HHCofree k a) = HHCofree k (h scls1 f g a)
    where
      h :: c f => (c f :- Bifunctor f) -> (a -> a') -> (b -> b') -> f a b -> f a' b'
      h (Sub Dict) = bimap
      
instance SuperClass1 Profunctor c => Profunctor (HHCofree c g) where
  dimap f g (HHCofree k a) = HHCofree k (h scls1 f g a)
    where
      h :: c f => (c f :- Profunctor f) -> (a' -> a) -> (b -> b') -> f a b -> f a' b'
      h (Sub Dict) = dimap
      
instance SuperClass1 Strong c => Strong (HHCofree c f) where
  first' (HHCofree k a) = HHCofree k (h scls1 a)
    where
      h :: c g => (c g :- Strong g) -> g a b -> g (a, d) (b, d)
      h (Sub Dict) = first'
      
instance SuperClass1 Choice c => Choice (HHCofree c f) where
  left' (HHCofree k a) = HHCofree k (h scls1 a)
    where
      h :: c g => (c g :- Choice g) -> g a b -> g (Either a d) (Either b d)
      h (Sub Dict) = left'
      
instance SuperClass1 Closed c => Closed (HHCofree c f) where
  closed (HHCofree k a) = HHCofree k (h scls1 a)
    where
      h :: c g => (c g :- Closed g) -> g a b -> g (d -> a) (d -> b)
      h (Sub Dict) = closed