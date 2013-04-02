{-# LANGUAGE
    ConstraintKinds
  , RankNTypes
  , TypeOperators  
  , FlexibleInstances
  , GADTs
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.HCofree
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A cofree functor is right adjoint to a forgetful functor.
-- In this package the forgetful functor forgets class constraints.
--
-- Compared to @Data.Functor.Cofree@ we're going up a level.
-- These free functors go between categories of functors and the natural
-- transformations between them.
-----------------------------------------------------------------------------
module Data.Functor.HCofree where

import Control.Comonad
import Data.Foldable
import Data.Traversable
import Data.Functor.Identity

-- | Natural transformations.
type f :~> g = forall b. f b -> g b

-- | The higher order cofree functor for constraint @c@.
data HCofree c g a where
  HCofree :: (c f, Functor f) => (f :~> g) -> f a -> HCofree c g a

instance Functor (HCofree c g) where
  fmap f (HCofree k a) = HCofree k (fmap f a)

counit :: HCofree c g :~> g
counit (HCofree k fa) = k fa

leftAdjunct :: (c f, Functor f) => (f :~> g) -> f :~> HCofree c g
leftAdjunct k fa = HCofree k fa

-- | @unit = leftAdjunct id@
unit :: (c g, Functor g) => g :~> HCofree c g
unit = leftAdjunct id

-- | @rightAdjunct f = counit . f@
rightAdjunct :: (f :~> HCofree c g) -> f :~> g
rightAdjunct f = counit . f

hfmap :: (f :~> g) -> HCofree c f :~> HCofree c g
hfmap f (HCofree k a) = HCofree (f . k) a

liftCofree :: (c f, Functor f) => f a -> HCofree c f a
liftCofree = leftAdjunct id

lowerCofree :: HCofree c f a -> f a
lowerCofree = counit

coiter :: c Identity => (forall b. b -> f b) -> a -> HCofree c f a
coiter f = leftAdjunct (f . runIdentity) . Identity

instance Foldable (HCofree Foldable g) where
  foldMap f (HCofree _ a) = foldMap f a
instance Foldable (HCofree Traversable g) where
  foldMap f (HCofree _ a) = foldMap f a
instance Traversable (HCofree Traversable g) where
  traverse f (HCofree k a) = HCofree k <$> traverse f a

-- | The cofree comonad of a functor.
instance Comonad (HCofree Comonad g) where
  extract (HCofree _ a) = extract a
  extend f (HCofree k a) = HCofree k $ extend (f . HCofree k) a
  duplicate (HCofree k a) = HCofree k $ extend (HCofree k) a

unwrap :: HCofree Comonad g a -> g (HCofree Comonad g a)
unwrap = counit . duplicate