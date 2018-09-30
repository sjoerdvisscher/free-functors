{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# LANGUAGE
    RankNTypes
  , TypeOperators
  , ConstraintKinds
  , TemplateHaskell
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

import Language.Haskell.TH.Syntax (Q, Name, Dec)
import Data.Functor.Free.Internal

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


-- | Derive the instance of @`HFree` c f a@ for the class @c@,.
--
-- For example:
--
-- @deriveHFreeInstance ''Functor@
deriveHFreeInstance :: Name -> Q [Dec]
deriveHFreeInstance = deriveFreeInstance' ''HFree 'HFree 'runHFree

deriveFreeInstance' ''HFree 'HFree 'runHFree ''Functor
deriveFreeInstance' ''HFree 'HFree 'runHFree ''Applicative
deriveFreeInstance' ''HFree 'HFree 'runHFree ''Alternative

-- | The free monad of a functor.
deriveFreeInstance' ''HFree 'HFree 'runHFree ''Monad

-- HFree Monad is only a monad transformer if rightAdjunct is called with monad morphisms.
-- F.e. lift . return == return fails if the results are inspected with rightAdjunct (const Nothing).

deriveFreeInstance' ''HFree 'HFree 'runHFree ''Contravariant
deriveFreeInstance' ''HFree 'HFree 'runHFree ''Divisible
deriveFreeInstance' ''HFree 'HFree 'runHFree ''Decidable
