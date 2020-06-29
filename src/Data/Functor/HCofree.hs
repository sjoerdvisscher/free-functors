{-# LANGUAGE
    GADTs
  , RankNTypes
  , TypeOperators
  , ConstraintKinds
  , TemplateHaskell
  , UndecidableInstances
  , QuantifiedConstraints
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.HCofree
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A cofree functor is right adjoint to a forgetful functor.
-- In this package the forgetful functor forgets class constraints.
--
-- Compared to @Data.Functor.Cofree@ we're going up a level.
-- These free functors go between categories of functors and the natural
-- transformations between them.
-----------------------------------------------------------------------------
module Data.Functor.HCofree where

import Control.Comonad
import Control.Comonad.Trans.Class
import Data.Functor.Identity

import Language.Haskell.TH.Syntax
import Data.Functor.Cofree.Internal


-- | Natural transformations.
type f :~> g = forall b. f b -> g b

-- | The higher order cofree functor for constraint @c@.
data HCofree c g a where
  HCofree :: c f => (f :~> g) -> f a -> HCofree c g a


-- | Derive the instance of @`HCofree` c a@ for the class @c@.
--
-- For example:
--
-- @deriveHCofreeInstance ''Traversable@
deriveHCofreeInstance :: Name -> Q [Dec]
deriveHCofreeInstance = deriveCofreeInstance' ''HCofree 'HCofree


counit :: HCofree c g :~> g
counit (HCofree k fa) = k fa

leftAdjunct :: c f => (f :~> g) -> f :~> HCofree c g
leftAdjunct = HCofree

-- | @unit = leftAdjunct id@
unit :: c g => g :~> HCofree c g
unit = leftAdjunct id

-- | @rightAdjunct f = counit . f@
rightAdjunct :: (f :~> HCofree c g) -> f :~> g
rightAdjunct f = counit . f

transform :: (forall r. c r => (r :~> f) -> r :~> g) -> HCofree c f :~> HCofree c g
transform t (HCofree k a) = HCofree (t k) a

hfmap :: (f :~> g) -> HCofree c f :~> HCofree c g
hfmap f = transform (f .)

hextend :: (HCofree c f :~> g) -> HCofree c f :~> HCofree c g
hextend f = transform (\k -> f . leftAdjunct k)

liftCofree :: c f => f a -> HCofree c f a
liftCofree = leftAdjunct id

lowerCofree :: HCofree c f a -> f a
lowerCofree = counit

convert :: (c (t f), Comonad f, ComonadTrans t) => t f a -> HCofree c f a
convert = leftAdjunct lower

coiter :: c Identity => (forall b. b -> f b) -> a -> HCofree c f a
coiter f = leftAdjunct (f . runIdentity) . Identity

unwrap :: HCofree Comonad g a -> g (HCofree Comonad g a)
unwrap = counit . duplicate

deriveCofreeInstance' ''HCofree 'HCofree ''Functor
deriveCofreeInstance' ''HCofree 'HCofree ''Foldable
deriveCofreeInstance' ''HCofree 'HCofree ''Traversable

-- | The cofree comonad of a functor.
instance (c ~=> Comonad) => Comonad (HCofree c g) where
  extract (HCofree _ a) = extract a
  extend f (HCofree k a) = HCofree k $ extend (f . HCofree k) a
  duplicate (HCofree k a) = HCofree k $ extend (HCofree k) a
