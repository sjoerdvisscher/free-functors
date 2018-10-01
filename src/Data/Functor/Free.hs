{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-unused-matches #-}
{-# LANGUAGE
    RankNTypes
  , TypeFamilies
  , TypeOperators
  , DeriveFunctor
  , DeriveFoldable
  , ConstraintKinds
  , TemplateHaskell
  , DeriveTraversable
  , FlexibleInstances
  , UndecidableInstances
  , QuantifiedConstraints
  , MultiParamTypeClasses
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
  , deriveFreeInstance
  , deriveInstances
  , unit
  , rightAdjunct
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

  ) where

import Data.Function (fix)
import Data.Monoid (Ap(..))
import Data.Void
import Data.Traversable
import Control.Comonad

import Language.Haskell.TH.Syntax
import Data.Functor.Free.Internal
import Data.DeriveLiftedInstances (ShowsPrec(..), deriveInstance, apDeriv)


-- | The free functor for class @c@.
--
--   @Free c a@ is basically an expression tree with operations from class @c@
--   and variables/placeholders of type @a@, created with `unit`.
--   Monadic bind allows you to replace each of these variables with another sub-expression.
newtype Free c a = Free { runFree :: forall b. c b => (a -> b) -> b }

-- | `unit` allows you to create @`Free` c@ values, together with the operations from the class @c@.
unit :: a -> Free c a
unit a = Free $ \k -> k a

-- | `rightAdjunct` is the destructor of @`Free` c@ values.
rightAdjunct :: c b => (a -> b) -> Free c a -> b
rightAdjunct f g = runFree g f

-- | @counit = rightAdjunct id@
counit :: c a => Free c a -> a
counit = rightAdjunct id

-- | @leftAdjunct f = f . unit@
leftAdjunct :: (Free c a -> b) -> a -> b
leftAdjunct f = f . unit

-- | @transform f as = as >>= f unit@
--
-- @transform f . transform g = transform (g . f)@
transform :: (forall r. c r => (b -> r) -> a -> r) -> Free c a -> Free c b
transform t (Free f) = Free (f . t)


instance Functor (Free c) where
  fmap f = transform (. f)

instance Applicative (Free c) where
  pure = unit
  fs <*> as = transform (\k f -> rightAdjunct (k . f) as) fs

instance Monad (Free c) where
  return = unit
  as >>= f = transform (\k -> rightAdjunct k . f) as

instance (forall f x. Applicative f => c (Ap f (Free c x))) => Foldable (Free c) where
  foldMap = foldMapDefault

instance (forall f x. Applicative f => c (Ap f (Free c x))) => Traversable (Free c) where
  traverse f = getAp . rightAdjunct (Ap . fmap unit . f)

instance (Show a, c ShowsPrec) => Show (Free c a) where
  showsPrec p = showsPrec p . rightAdjunct (\a -> ShowsPrec $ \d -> showParen (d > 10) $ showString "pure " . showsPrec 11 a)

  
newtype Extract a = Extract { getExtract :: a }
newtype Duplicate f a = Duplicate { getDuplicate :: f (f a) }
instance (forall x. c (Extract x), forall x. c (Duplicate (Free c) x))
  => Comonad (Free c) where
  extract = getExtract . rightAdjunct Extract
  duplicate = getDuplicate . rightAdjunct (Duplicate . unit . unit)


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

-- | Derive the instance of @`Free` c a@ for the class @c@.
--
-- For example:
--
-- @deriveFreeInstance ''Num@
deriveFreeInstance :: Name -> Q [Dec]
deriveFreeInstance = deriveFreeInstance' ''Free 'Free 'runFree

--- | Derive the instances of @`Free` c a@ for the class @c@, `Show`, `Foldable` and `Traversable`.
-- 
-- For example:
--
-- @deriveInstances ''Num@
deriveInstances :: Name -> Q [Dec]
deriveInstances = deriveInstances' ''Free 'Free 'runFree

deriveFreeInstance' ''Free 'Free 'runFree ''Num
deriveFreeInstance' ''Free 'Free 'runFree ''Fractional
deriveFreeInstance' ''Free 'Free 'runFree ''Floating
deriveFreeInstance' ''Free 'Free 'runFree ''Semigroup
deriveFreeInstance' ''Free 'Free 'runFree ''Monoid

deriveInstance apDeriv [t|forall f a c. (Applicative f, Fractional a) => Fractional (Ap f a)|]
deriveInstance apDeriv [t|forall f a c. (Applicative f, Floating a) => Floating (Ap f a)|]