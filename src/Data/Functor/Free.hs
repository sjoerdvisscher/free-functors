{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE
    ConstraintKinds
  , GADTs
  , RankNTypes
  , TypeOperators
  , FlexibleInstances
  , MultiParamTypeClasses
  , UndecidableInstances
  , ScopedTypeVariables
  , DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  , TemplateHaskell
  , PolyKinds
  , TypeFamilies
  , DataKinds
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
-- In this package the forgetful functor forgets class constraints.
-----------------------------------------------------------------------------
module Data.Functor.Free (

    Free(..)
  , deriveInstances
  , unit
  , rightAdjunct
  , rightAdjunctF
  , counit
  , leftAdjunct
  , transform
  , unfold
  , convert
  , convertClosed
  , Extract(..)
  , Duplicate(..)

  -- * Coproducts
  , Coproduct
  , coproduct
  , inL
  , inR
  , InitialObject
  , initial
  
  -- * Internal
  , ShowHelper(..)

  ) where

import Data.Function

import Data.Void

import Language.Haskell.TH.Syntax

import Data.Functor.Free.TH

-- | @unfold f = coproduct (unfold f) unit . f@
--
-- `inL` and `inR` are useful here. For example, the following creates the list @[1..10]@ as a @Free Monoid@:
--
-- @unfold (\b -> if b == 0 then mempty else `inL` (b - 1) \<> `inR` b) 10@
unfold :: (b -> Coproduct c b a) -> b -> Free c a
unfold f = fix $ \go -> transform (\k -> either (rightAdjunct k . go) k) . f

-- | @convert = rightAdjunct pure@
convert :: (c (f a), Applicative f) => Free c a -> f a
convert = rightAdjunct pure

-- | @convertClosed = rightAdjunct absurd@
convertClosed :: c r => Free c Void -> r
convertClosed = rightAdjunct absurd


-- | Products of @Monoid@s are @Monoid@s themselves. But coproducts of @Monoid@s are not.
-- However, the free @Monoid@ applied to the coproduct /is/ a @Monoid@, and it is the coproduct in the category of @Monoid@s.
-- This is also called the free product, and generalizes to any algebraic class.
type Coproduct c m n = Free c (Either m n)

coproduct :: c r => (m -> r) -> (n -> r) -> Coproduct c m n -> r
coproduct m n = rightAdjunct (either m n)

inL :: m -> Coproduct c m n
inL = unit . Left

inR :: n -> Coproduct c m n
inR = unit . Right

type InitialObject c = Free c Void

initial :: c r => InitialObject c -> r
initial = rightAdjunct absurd


-- | Derive the instances of @`Free` c a@ for the class @c@, `Show`, `Foldable` and `Traversable`.
--
-- For example:
--
-- @deriveInstances ''Num@
deriveInstances :: Name -> Q [Dec]
deriveInstances = deriveInstances' True

deriveInstances' False ''Num
deriveInstances' False ''Fractional
deriveInstances' False ''Floating
deriveInstances' False ''Semigroup
deriveInstances' False ''Monoid
