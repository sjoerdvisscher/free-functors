{-# LANGUAGE
    GADTs
  , RankNTypes
  , TypeOperators
  , ConstraintKinds
  , UndecidableInstances
  , QuantifiedConstraints
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
import Data.Foldable
import Data.Functor.Identity

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

instance (forall x. c x => Functor x) => Functor (HCofree c g) where
  fmap f (HCofree k a) = HCofree k (fmap f a)
  a <$ HCofree k b = HCofree k (a <$ b)

instance (forall x. c x => Foldable x) => Foldable (HCofree c g) where
  foldMap f (HCofree _ a) = foldMap f a
  fold (HCofree _ a) = fold a
  foldr f z (HCofree _ a) = foldr f z a
  foldl f z (HCofree _ a) = foldl f z a
  foldl' f z (HCofree _ a) = foldl' f z a
  foldr1 f (HCofree _ a) = foldr1 f a
  foldr' f z (HCofree _ a) = foldr' f z a
  foldl1 f (HCofree _ a) = foldl1 f a
  toList (HCofree _ a) = toList a
  null (HCofree _ a) = null a
  length (HCofree _ a) = length a
  elem e (HCofree _ a) = elem e a
  maximum (HCofree _ a) = maximum a
  minimum (HCofree _ a) = minimum a
  sum (HCofree _ a) = sum a
  product (HCofree _ a) = product a

instance (forall x. c x => Traversable x) => Traversable (HCofree c g) where
  traverse f (HCofree k a) = HCofree k <$> traverse f a
  sequenceA (HCofree k a) = HCofree k <$> sequenceA a
  mapM f (HCofree k a) = HCofree k <$> mapM f a
  sequence (HCofree k a) = HCofree k <$> sequence a

-- | The cofree comonad of a functor.
instance (forall x. c x => Comonad x) => Comonad (HCofree c g) where
  extract (HCofree _ a) = extract a
  extend f (HCofree k a) = HCofree k $ extend (f . HCofree k) a
  duplicate (HCofree k a) = HCofree k $ extend (HCofree k) a
