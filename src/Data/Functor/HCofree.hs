{-# LANGUAGE
    GADTs
  , RankNTypes
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
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
import Control.Comonad.Trans.Class
import Data.Functor.Identity
import Data.Constraint
import Data.Constraint.Class1

-- | Natural transformations.
type f :~> g = forall b. f b -> g b

-- | The higher order cofree functor for constraint @c@.
data HCofree c g a where
  HCofree :: c f => (f :~> g) -> f a -> HCofree c g a


counit :: HCofree c g :~> g
counit (HCofree k fa) = k fa

leftAdjunct :: c f => (f :~> g) -> f :~> HCofree c g
leftAdjunct k fa = HCofree k fa

-- | @unit = leftAdjunct id@
unit :: c g => g :~> HCofree c g
unit = leftAdjunct id

-- | @rightAdjunct f = counit . f@
rightAdjunct :: (f :~> HCofree c g) -> f :~> g
rightAdjunct f = counit . f

transform :: (forall r. c r => (r :~> f) -> r :~> g) -> HCofree c f :~> HCofree c g
transform t (HCofree k a) = HCofree (t k) a

hfmap :: (f :~> g) -> HCofree c f :~> HCofree c g
hfmap f = transform (\k -> f . k)

hextend :: (HCofree c f :~> g) -> HCofree c f :~> HCofree c g
hextend f = transform (\k -> f . leftAdjunct k)

liftCofree :: c f => f a -> HCofree c f a
liftCofree = leftAdjunct id

lowerCofree :: HCofree c f a -> f a
lowerCofree = counit

convert :: (c (t f), Comonad f, ComonadTrans t) => t f a -> HCofree c f a
convert = leftAdjunct lower

coiter :: c Identity => (forall b. b -> f b) -> a -> HCofree c f a
coiter f = leftAdjunct (f . runIdentity) . Identity

unwrap :: HCofree Comonad g a -> g (HCofree Comonad g a)
unwrap = counit . duplicate

instance SuperClass1 Functor c => Functor (HCofree c g) where
  fmap f (HCofree k a) = HCofree k (h scls1 f a)
    where
      h :: c f => (c f :- Functor f) -> (a -> b) -> f a -> f b
      h (Sub Dict) = fmap

instance SuperClass1 Foldable c => Foldable (HCofree c g) where
  foldMap f (HCofree _ a) = h scls1 f a
    where
      h :: (c f, Monoid m) => (c f :- Foldable f) -> (a -> m) -> f a -> m
      h (Sub Dict) = foldMap

instance SuperClass1 Traversable c => Traversable (HCofree c g) where
  traverse f (HCofree k a) = HCofree k <$> h scls1 f a
    where
      h :: (c t, Applicative f) => (c t :- Traversable t) -> (a -> f b) -> t a -> f (t b)
      h (Sub Dict) = traverse

-- | The cofree comonad of a functor.
instance SuperClass1 Comonad c => Comonad (HCofree c g) where
  extract (HCofree _ a) = h scls1 a
    where
      h :: c f => (c f :- Comonad f) -> f a -> a
      h (Sub Dict) = extract
  extend f (HCofree k a) = HCofree k $ h scls1 (f . HCofree k) a
    where
      h :: c f => (c f :- Comonad f) -> (f a -> b) -> (f a -> f b)
      h (Sub Dict) = extend
