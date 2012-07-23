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
-- Module      :  Data.Functor.Cofree
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A cofree functor is right adjoint to a forgetful functor.
-- In this package the forgetful functor forgets class constraints.
-----------------------------------------------------------------------------
module Data.Functor.Cofree where
  
import Control.Monad
import Control.Comonad
import Control.Applicative

import Data.Constraint
import Data.Constraint.Forall

import Data.Functor.Identity
import Data.Functor.Compose


-- | The cofree functor for constraint @c@.
data Cofree c b where
  Cofree :: c a => (a -> b) -> a -> Cofree c b

leftAdjunct :: c a => (a -> b) -> a -> Cofree c b
leftAdjunct f a = Cofree f a

rightAdjunct :: (a -> Cofree c b) -> a -> b
rightAdjunct f a = case f a of Cofree k a' -> k a'

leftAdjunct' :: ForallF c f => (f a -> b) -> f a -> Cofree c b
leftAdjunct' = h instF leftAdjunct
  where
    h :: ForallF c f
      => (ForallF c f :- c (f a))
      -> (c (f a) => (f a -> b) -> f a -> Cofree c b)
      -> (f a -> b) -> f a -> Cofree c b
    h (Sub Dict) f = f

instance Functor (Cofree c) where
  fmap f (Cofree k a) = Cofree (f . k) a

instance ForallF c (Cofree c) => Comonad (Cofree c) where
  extract = rightAdjunct id
  extend = leftAdjunct'

instance (ForallF c Identity, ForallF c (Cofree c), ForallF c (Compose (Cofree c) (Cofree c)))
  => Applicative (Cofree c) where
  pure = leftAdjunct' runIdentity . Identity
  (<*>) = ap

instance (ForallF c Identity, ForallF c (Cofree c), ForallF c (Compose (Cofree c) (Cofree c)))
  => Monad (Cofree c) where
  return = pure
  m >>= g = leftAdjunct' (extract . extract . getCompose) (Compose $ fmap g m)

convert :: (c (w a), Comonad w) => w a -> Cofree c a
convert wa = Cofree extract wa