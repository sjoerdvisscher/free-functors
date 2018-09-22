{-# LANGUAGE
    ConstraintKinds
  , GADTs
  , UndecidableInstances
  , QuantifiedConstraints
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

import Data.Functor.Identity
import Data.Functor.Compose


-- | The cofree functor for constraint @c@.
data Cofree c b where
  Cofree :: c a => (a -> b) -> a -> Cofree c b


counit :: Cofree c b -> b
counit (Cofree k a) = k a

leftAdjunct :: c a => (a -> b) -> a -> Cofree c b
leftAdjunct f a = Cofree f a

-- | @unit = leftAdjunct id@
unit :: c b => b -> Cofree c b
unit = leftAdjunct id

-- | @rightAdjunct f = counit . f@
rightAdjunct :: (a -> Cofree c b) -> a -> b
rightAdjunct f = counit . f

instance Functor (Cofree c) where
  fmap f (Cofree k a) = Cofree (f . k) a

instance Comonad (Cofree c) where
  extract = counit
  duplicate (Cofree k a) = Cofree (leftAdjunct k) a

instance (forall x. c (Identity x), forall x. c (Compose (Cofree c) (Cofree c) x))
  => Applicative (Cofree c) where
  pure = leftAdjunct runIdentity . Identity
  (<*>) = ap

instance (forall x. c (Identity x), forall x. c (Compose (Cofree c) (Cofree c) x))
  => Monad (Cofree c) where
  return = pure
  m >>= g = leftAdjunct (extract . extract . getCompose) (Compose $ fmap g m)

convert :: (c (w a), Comonad w) => w a -> Cofree c a
convert = leftAdjunct extract


-- * Products

type Product c m n = Cofree c (m, n)

product :: c a => (a -> m) -> (a -> n) -> a -> Product c m n
product m n = leftAdjunct (\a -> (m a, n a))

outL :: Product c m n -> m
outL = fst . counit

outR :: Product c m n -> n
outR = snd . counit

type TerminalObject c = Cofree c ()

terminal :: c a => a -> TerminalObject c
terminal = leftAdjunct (const ())
