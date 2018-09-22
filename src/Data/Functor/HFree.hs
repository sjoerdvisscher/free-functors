{-# LANGUAGE
    RankNTypes
  , TypeOperators
  , ConstraintKinds
  , UndecidableInstances
  , QuantifiedConstraints
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.HFree
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A free functor is left adjoint to a forgetful functor.
-- In this package the forgetful functor forgets class constraints.
--
-- Compared to @Data.Functor.Free@ we're going up a level.
-- These free functors go between categories of functors and the natural
-- transformations between them.
-----------------------------------------------------------------------------
module Data.Functor.HFree where

import Control.Applicative
import Control.Monad.Trans.Class
import Data.Functor.Identity
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

-- | Natural transformations.
type f :~> g = forall b. f b -> g b

-- | The higher order free functor for constraint @c@.
newtype HFree c f a = HFree { runHFree :: forall g. c g => (f :~> g) -> g a }

unit :: f :~> HFree c f
unit fa = HFree $ \k -> k fa

rightAdjunct :: c g => (f :~> g) -> HFree c f :~> g
rightAdjunct f h = runHFree h f

-- | @counit = rightAdjunct id@
counit :: c f => HFree c f :~> f
counit = rightAdjunct id

-- | @leftAdjunct f = f . unit@
leftAdjunct :: (HFree c f :~> g) -> f :~> g
leftAdjunct f = f . unit

transform :: (forall r. c r => (g :~> r) -> f :~> r) -> HFree c f :~> HFree c g
transform t h = HFree $ \k -> rightAdjunct (t k) h
-- transform t = HFree . (. t) . runHFree

hfmap :: (f :~> g) -> HFree c f :~> HFree c g
hfmap f = transform (\k -> k . f)

bind :: (f :~> HFree c g) -> HFree c f :~> HFree c g
bind f = transform (\k -> rightAdjunct k . f)

liftFree :: f a -> HFree c f a
liftFree = unit

lowerFree :: c f => HFree c f a -> f a
lowerFree = counit

convert :: (c (t f), Monad f, MonadTrans t) => HFree c f a -> t f a
convert = rightAdjunct lift

iter :: c Identity => (forall b. f b -> b) -> HFree c f a -> a
iter f = runIdentity . rightAdjunct (Identity . f)

wrap :: f (HFree Monad f a) -> HFree Monad f a
wrap as = unit as >>= id


instance (forall x. c x => Functor x) => Functor (HFree c f) where
  fmap f (HFree g) = HFree $ \k -> fmap f (g k)
  a <$ HFree g = HFree $ \k -> a <$ g k

instance (forall x. c x => Applicative x) => Applicative (HFree c f) where
  pure a = HFree $ const (pure a)
  HFree f <*> HFree g = HFree $ \k -> f k <*> g k
  HFree f <* HFree g = HFree $ \k -> f k <* g k
  HFree f *> HFree g = HFree $ \k -> f k *> g k
  liftA2 f (HFree g) (HFree h) = HFree $ \k -> liftA2 f (g k) (h k)

instance (forall x. c x => Alternative x) => Alternative (HFree c f) where
  empty = HFree $ const empty
  HFree f <|> HFree g = HFree $ \k -> f k <|> g k
  many (HFree f) = HFree $ \k -> many (f k)
  some (HFree f) = HFree $ \k -> some (f k)

-- | The free monad of a functor.
instance (forall x. c x => Monad x) => Monad (HFree c f) where
  return = pure
  HFree f >>= g = HFree $ \k -> f k >>= rightAdjunct k . g
  HFree f >> HFree g = HFree $ \k -> f k >> g k
  fail s = HFree $ const (fail s)

-- HFree Monad is only a monad transformer if rightAdjunct is called with monad morphisms.
-- F.e. lift . return == return fails if the results are inspected with rightAdjunct (const Nothing).

instance (forall x. c x => Contravariant x) => Contravariant (HFree c f) where
  contramap f (HFree g) = HFree $ \k -> contramap f (g k)
  a >$ HFree g = HFree $ \k -> a >$ g k

instance (forall x. c x => Divisible x) => Divisible (HFree c f) where
  divide f (HFree a) (HFree b) = HFree $ \k -> divide f (a k) (b k)
  conquer = HFree $ const conquer

instance (forall x. c x => Decidable x) => Decidable (HFree c f) where
  choose f (HFree a) (HFree b) = HFree $ \k -> choose f (a k) (b k)
  lose f = HFree $ const (lose f)
