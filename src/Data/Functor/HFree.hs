{-# LANGUAGE
    RankNTypes
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , ScopedTypeVariables
  , UndecidableInstances
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
import Data.Constraint
import Data.Constraint.Class1
import Data.Void


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


instance SuperClass1 Functor c => Functor (HFree c f) where
  fmap f (HFree g) = HFree $ \k -> h scls1 f (g k)
    where
      h :: c g => (c g :- Functor g) -> (a -> b) -> g a -> g b
      h (Sub Dict) = fmap

instance SuperClass1 Applicative c => Applicative (HFree c f) where
  pure a = HFree $ const (h scls1 a)
    where
      h :: c g => (c g :- Applicative g) -> a -> g a
      h (Sub Dict) = pure
  HFree f <*> HFree g = HFree $ \k -> h scls1 (f k) (g k)
    where
      h :: c g => (c g :- Applicative g) -> g (a -> b) -> g a -> g b
      h (Sub Dict) = (<*>)

instance SuperClass1 Alternative c => Alternative (HFree c f) where
  empty = HFree $ const (h scls1)
    where
      h :: c g => (c g :- Alternative g) -> g a
      h (Sub Dict) = empty
  HFree f <|> HFree g = HFree $ \k -> h scls1 (f k) (g k)
    where
      h :: c g => (c g :- Alternative g) -> g a -> g a -> g a
      h (Sub Dict) = (<|>)

-- | The free monad of a functor.
instance SuperClass1 Monad c => Monad (HFree c f) where
  return = pure
  HFree f >>= g = HFree $ \k -> h scls1 (f k) (rightAdjunct k . g)
    where
      h :: c g => (c g :- Monad g) -> g a -> (a -> g b) -> g b
      h (Sub Dict) = (>>=)

-- HFree Monad is only a monad transformer if rightAdjunct is called with monad morphisms.
-- F.e. lift . return == return fails if the results are inspected with rightAdjunct (const Nothing).

instance SuperClass1 Contravariant c => Contravariant (HFree c f) where
  contramap f (HFree g) = HFree $ \k -> h scls1 f (g k)
    where
      h :: c g => (c g :- Contravariant g) -> (b -> a) -> g a -> g b
      h (Sub Dict) = contramap

instance SuperClass1 Divisible c => Divisible (HFree c f) where
  divide f (HFree a) (HFree b) = HFree $ \k -> h scls1 f (a k) (b k)
    where
      h :: c g => (c g :- Divisible g) -> (a -> (b, d)) -> g b -> g d -> g a
      h (Sub Dict) = divide
  conquer = HFree $ const (h scls1)
    where
      h :: c g => (c g :- Divisible g) -> g a
      h (Sub Dict) = conquer

instance SuperClass1 Decidable c => Decidable (HFree c f) where
  choose f (HFree a) (HFree b) = HFree $ \k -> h scls1 f (a k) (b k)
    where
      h :: c g => (c g :- Decidable g) -> (a -> Either b d) -> g b -> g d -> g a
      h (Sub Dict) = choose
  lose f = HFree $ const (h scls1 f)
    where
      h :: c g => (c g :- Decidable g) -> (a -> Void) -> g a
      h (Sub Dict) = lose
