{-# LANGUAGE
    ConstraintKinds
  , RankNTypes
  , TypeOperators  
  , FlexibleInstances
  , MultiParamTypeClasses
  , UndecidableInstances
  , ScopedTypeVariables
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Free
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A free functor is left adjoint to a forgetful functor.
-- In this module the forgetful functor forgets class constraints.
-----------------------------------------------------------------------------
module Data.Functor.Free where
  
import Data.Constraint
import Data.Constraint.Forall

import Control.Monad
import Control.Comonad

import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Foldable
import Data.Traversable



newtype Free c a = Free { runFree :: forall b. c b => (a -> b) -> b }

leftAdjunct :: (Free c a -> b) -> a -> b
leftAdjunct f a = f (Free ($ a))

rightAdjunct :: c b => (a -> b) -> Free c a -> b
rightAdjunct f g = runFree g f

rightAdjunct' :: ForallF c f => (a -> f b) -> Free c a -> f b
rightAdjunct' = h instF rightAdjunct
  where
    h :: ForallF c f
      => (ForallF c f :- c (f b))
      -> (c (f b) => (a -> f b) -> Free c a -> f b)
      -> (a -> f b) -> Free c a -> f b
    h (Sub Dict) f = f

rightAdjunct'' :: ForallT c t => (a -> t f b) -> Free c a -> t f b
rightAdjunct'' = h instT rightAdjunct
  where
    h :: ForallT c t
      => (ForallT c t :- c (t f b))
      -> (c (t f b) => (a -> t f b) -> Free c a -> t f b)
      -> (a -> t f b) -> Free c a -> t f b
    h (Sub Dict) f = f

instance Functor (Free c) where
  fmap f (Free g) = Free (g . (. f))

instance Applicative (Free c) where
  pure = leftAdjunct id
  fs <*> as = Free $ \k -> runFree fs (\f -> runFree as (k . f))

instance ForallF c (Free c) => Monad (Free c) where
  return = pure
  (>>=) = flip rightAdjunct'

instance (ForallF c Identity, ForallF c (Free c), ForallF c (Compose (Free c) (Free c)))
  => Comonad (Free c) where
  extract = runIdentity . rightAdjunct' Identity
  extend g = fmap g . getCompose . rightAdjunct' (Compose . return . return)

newtype LiftAFree c f a = LiftAFree { getLiftAFree :: f (Free c a) }

instance ForallT c (LiftAFree c) => Foldable (Free c) where
  foldMap = foldMapDefault

instance ForallT c (LiftAFree c) => Traversable (Free c) where
  traverse f = getLiftAFree . rightAdjunct'' (LiftAFree . fmap pure . f)

convert :: (c (f a), Applicative f) => Free c a -> f a
convert = rightAdjunct pure

