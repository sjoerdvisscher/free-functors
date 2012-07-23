{-# LANGUAGE
    ConstraintKinds
  , RankNTypes
  , TypeOperators
  , FlexibleInstances
  , GADTs
  , MultiParamTypeClasses
  , UndecidableInstances
  , ScopedTypeVariables
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
  
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.Class


-- | Natural transformations.
type f :~> g = forall b. f b -> g b

-- | The higher order free functor for constraint @c@.
newtype HFree c f a = HFree { runHFree :: forall g. (c g, Functor g) => (f :~> g) -> g a }

leftAdjunct :: (HFree c f :~> g) -> f :~> g
leftAdjunct f fa = f (HFree $ \k -> k fa)

rightAdjunct :: (c g, Functor g) => (f :~> g) -> HFree c f :~> g
rightAdjunct f h = runHFree h f

instance Functor (HFree c f) where
  fmap f (HFree g) = HFree (fmap f . g)

hfmap :: (f :~> g) -> HFree c f :~> HFree c g
hfmap f (HFree g) = HFree $ \k -> g (k . f)

liftFree :: f a -> HFree c f a
liftFree = leftAdjunct id

lowerFree :: (c f, Functor f) => HFree c f a -> f a
lowerFree = rightAdjunct id

convert :: (c (t f), Functor (t f), Monad f, MonadTrans t) => HFree c f a -> t f a
convert = rightAdjunct lift

-- | The free monad of a functor.
instance Monad (HFree Monad f) where
  return a = HFree $ const (return a)
  HFree f >>= g = HFree $ \k -> f k >>= (\a -> runHFree (g a) k)

instance Applicative (HFree Applicative f) where
  pure a = HFree $ const (pure a)
  HFree f <*> HFree g = HFree $ \k -> f k <*> g k

instance Applicative (HFree Alternative f) where
  pure a = HFree $ const (pure a)
  HFree f <*> HFree g = HFree $ \k -> f k <*> g k
instance Alternative (HFree Alternative f) where
  empty = HFree $ const empty
  HFree f <|> HFree g = HFree $ \k -> f k <|> g k