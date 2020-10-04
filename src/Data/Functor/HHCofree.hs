{-# LANGUAGE
    GADTs
  , RankNTypes
  , TypeOperators
  , TemplateHaskell
  , ConstraintKinds
  , FlexibleContexts
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , MultiParamTypeClasses
  , QuantifiedConstraints
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.HHCofree
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A cofree functor is right adjoint to a forgetful functor.
-- In this package the forgetful functor forgets class constraints.
--
-- Compared to @Data.Functor.HCofree@ we have 2 two parameters.
-----------------------------------------------------------------------------
module Data.Functor.HHCofree where

import Prelude hiding ((.), id)

import Control.Category
import Data.Bifunctor
import Data.Bifunctor.Functor
import Data.Profunctor
import Data.Profunctor.Monad

import Language.Haskell.TH.Syntax
import Data.Functor.Cofree.Internal


-- | Natural transformations.
type f :~~> g = forall c d. f c d -> g c d

-- | The higher order cofree functor for constraint @c@.
data HHCofree c g a b where
  HHCofree :: c f => (f :~~> g) -> f a b -> HHCofree c g a b


-- | Derive the instance of @`HHCofree` c a@ for the class @c@.
--
-- For example:
--
-- @deriveHHCofreeInstance ''Profunctor@
deriveHHCofreeInstance :: Name -> Q [Dec]
deriveHHCofreeInstance = deriveCofreeInstance' ''HHCofree 'HHCofree


counit :: HHCofree c g :~~> g
counit (HHCofree k fa) = k fa

leftAdjunct :: c f => (f :~~> g) -> f :~~> HHCofree c g
leftAdjunct f = HHCofree f

-- | @unit = leftAdjunct id@
unit :: c g => g :~~> HHCofree c g
unit = leftAdjunct id

-- | @rightAdjunct f = counit . f@
rightAdjunct :: (f :~~> HHCofree c g) -> f :~~> g
rightAdjunct f = counit . f

transform :: (forall r. c r => (r :~~> f) -> r :~~> g) -> HHCofree c f :~~> HHCofree c g
transform t (HHCofree k a) = HHCofree (t k) a

hfmap :: (f :~~> g) -> HHCofree c f :~~> HHCofree c g
hfmap f = transform (\g -> f . g)

hextend :: (HHCofree c f :~~> g) -> HHCofree c f :~~> HHCofree c g
hextend f = transform (\k -> f . leftAdjunct k)


instance BifunctorFunctor (HHCofree c) where
  bifmap = hfmap

instance BifunctorComonad (HHCofree c) where
  biextract = counit
  biextend = hextend

instance ProfunctorFunctor (HHCofree c) where
  promap = hfmap

instance ProfunctorComonad (HHCofree c) where
  proextract = counit
  produplicate = hextend id


deriveCofreeInstance' ''HHCofree 'HHCofree ''Bifunctor
deriveCofreeInstance' ''HHCofree 'HHCofree ''Profunctor
deriveCofreeInstance' ''HHCofree 'HHCofree ''Strong
deriveCofreeInstance' ''HHCofree 'HHCofree ''Choice
deriveCofreeInstance' ''HHCofree 'HHCofree ''Closed
