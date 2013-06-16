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

counit :: Cofree c b -> b
counit (Cofree k a) = k a

leftAdjunct :: c a => (a -> b) -> a -> Cofree c b
leftAdjunct f a = Cofree f a

leftAdjunctF :: ForallF c f => (f a -> b) -> f a -> Cofree c b
leftAdjunctF = h instF leftAdjunct
  where
    h :: ForallF c f
      => (ForallF c f :- c (f a))
      -> (c (f a) => (f a -> b) -> f a -> Cofree c b)
      -> (f a -> b) -> f a -> Cofree c b
    h (Sub Dict) f = f

-- | @unit = leftAdjunct id@
unit :: c b => b -> Cofree c b
unit = leftAdjunct id

-- | @rightAdjunct f = counit . f@
rightAdjunct :: (a -> Cofree c b) -> a -> b
rightAdjunct f = counit . f

instance Functor (Cofree c) where
  fmap f (Cofree k a) = Cofree (f . k) a

instance ForallF c (Cofree c) => Comonad (Cofree c) where
  extract = counit
  extend = leftAdjunctF

instance (ForallF c Identity, ForallF c (Cofree c), ForallF c (Compose (Cofree c) (Cofree c)))
  => Applicative (Cofree c) where
  pure = leftAdjunctF runIdentity . Identity
  (<*>) = ap

instance (ForallF c Identity, ForallF c (Cofree c), ForallF c (Compose (Cofree c) (Cofree c)))
  => Monad (Cofree c) where
  return = pure
  m >>= g = leftAdjunctF (extract . extract . getCompose) (Compose $ fmap g m)

convert :: (c (w a), Comonad w) => w a -> Cofree c a
convert = leftAdjunct extract


-- * Products

type Product c m n = Cofree c (m, n)

product :: c a => (a -> m) -> (a -> n) -> a -> Product c m n
product m n = leftAdjunct (\a -> (m a, n a))

projL :: Product c m n -> m
projL = fst . counit

projR :: Product c m n -> n
projR = snd . counit

type TerminalObject c = Cofree c ()

terminal :: c a => a -> TerminalObject c
terminal = leftAdjunct (const ())