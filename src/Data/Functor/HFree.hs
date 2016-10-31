{-# LANGUAGE
    ConstraintKinds
  , RankNTypes
  , TypeOperators
  , FlexibleInstances
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
import Control.Monad
import Control.Monad.Trans.Class
import Data.Functor.Identity


-- | Natural transformations.
type f :~> g = forall b. f b -> g b

-- | The higher order free functor for constraint @c@.
newtype HFree c f a = HFree { runHFree :: forall g. (c g, Functor g) => (f :~> g) -> g a }

unit :: f :~> HFree c f
unit fa = HFree $ \k -> k fa

rightAdjunct :: (c g, Functor g) => (f :~> g) -> HFree c f :~> g
rightAdjunct f h = runHFree h f

-- | @counit = rightAdjunct id@
counit :: (c f, Functor f) => HFree c f :~> f
counit = rightAdjunct id

-- | @leftAdjunct f = f . unit@
leftAdjunct :: (HFree c f :~> g) -> f :~> g
leftAdjunct f = f . unit

instance Functor (HFree c f) where
  fmap f h = HFree (\s -> fmap f (runHFree h s))

hfmap :: (f :~> g) -> HFree c f :~> HFree c g
hfmap f (HFree g) = HFree $ \k -> g (k . f)

liftFree :: f a -> HFree c f a
liftFree = unit

lowerFree :: (c f, Functor f) => HFree c f a -> f a
lowerFree = counit

convert :: (c (t f), Functor (t f), Monad f, MonadTrans t) => HFree c f a -> t f a
convert = rightAdjunct lift

iter :: c Identity => (forall b. f b -> b) -> HFree c f a -> a
iter f = runIdentity . rightAdjunct (Identity . f)

instance Applicative (HFree Monad f) where
  pure = return
  (<*>) = ap
  
-- | The free monad of a functor.
instance Monad (HFree Monad f) where
  return a = HFree $ const (return a)
  HFree f >>= g = HFree $ \k -> f k >>= (rightAdjunct k . g)
-- HFree Monad is only a monad transformer if rightAdjunct is called with monad morphisms.
-- F.e. lift . return == return fails if the results are inspected with rightAdjunct (const Nothing).
-- instance MonadTrans (HFree Monad) where
--   lift = liftFree
  
instance Applicative (HFree Applicative f) where
  pure a = HFree $ const (pure a)
  HFree f <*> HFree g = HFree $ \k -> f k <*> g k

instance Applicative (HFree Alternative f) where
  pure a = HFree $ const (pure a)
  HFree f <*> HFree g = HFree $ \k -> f k <*> g k
instance Alternative (HFree Alternative f) where
  empty = HFree $ const empty
  HFree f <|> HFree g = HFree $ \k -> f k <|> g k
  
wrap :: f (HFree Monad f a) -> HFree Monad f a
wrap = join . unit
