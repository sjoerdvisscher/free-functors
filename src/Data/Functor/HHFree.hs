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
-- Module      :  Data.Functor.HHFree
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A free functor is left adjoint to a forgetful functor.
-- In this package the forgetful functor forgets class constraints.
--
-- Compared to @Data.Functor.HFree@ we have 2 two parameters.
-----------------------------------------------------------------------------
module Data.Functor.HHFree where

import Prelude hiding ((.), id)

import Control.Arrow
import Control.Category
import Data.Bifunctor (Bifunctor)
import Data.Bifunctor.Functor
import Data.Biapplicative (Biapplicative)
import Data.Profunctor
import Data.Profunctor.Monad

import Language.Haskell.TH.Syntax (Q, Name, Dec)
import Data.Functor.Free.Internal


-- | Natural transformations.
type f :~~> g = forall a b. f a b -> g a b

-- | The higher order free functor over two type parameters for constraint @c@.
newtype HHFree c f a b = HHFree { runHHFree :: forall g. c g => (f :~~> g) -> g a b }

unit :: f :~~> HHFree c f
unit fa = HHFree $ \k -> k fa

rightAdjunct :: c g => (f :~~> g) -> HHFree c f :~~> g
rightAdjunct f h = runHHFree h f

-- | @counit = rightAdjunct id@
counit :: c f => HHFree c f :~~> f
counit = rightAdjunct id

-- | @leftAdjunct f = f . unit@
leftAdjunct :: (HHFree c f :~~> g) -> f :~~> g
leftAdjunct f = f . unit

transform :: (forall r. c r => (g :~~> r) -> f :~~> r) -> HHFree c f :~~> HHFree c g
transform t h = HHFree $ \k -> rightAdjunct (t k) h
-- transform t = HHFree . (. t) . runHHFree

hfmap :: (f :~~> g) -> HHFree c f :~~> HHFree c g
hfmap f = transform (\k -> k . f)

bind :: (f :~~> HHFree c g) -> HHFree c f :~~> HHFree c g
bind f = transform (\k -> rightAdjunct k . f)

instance BifunctorFunctor (HHFree c) where
  bifmap = hfmap

instance BifunctorMonad (HHFree c) where
  bireturn = unit
  bibind = bind

instance ProfunctorFunctor (HHFree c) where
  promap = hfmap

instance ProfunctorMonad (HHFree c) where
  proreturn = unit
  projoin = bind id


-- | Derive the instance of @`HHFree` c f a b@ for the class @c@,.
--
-- For example:
--
-- @deriveHHFreeInstance ''Category@
deriveHHFreeInstance :: Name -> Q [Dec]
deriveHHFreeInstance = deriveFreeInstance' ''HHFree 'HHFree 'runHHFree

deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Category
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Arrow
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''ArrowZero
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''ArrowPlus
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''ArrowChoice
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''ArrowLoop

instance (forall x. c x => ArrowApply x) => ArrowApply (HHFree c f) where
  app = HHFree $ \k -> app . arr (first (rightAdjunct k))

deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Bifunctor
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Biapplicative
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Profunctor
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Strong
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Choice
deriveFreeInstance' ''HHFree 'HHFree 'runHHFree ''Closed