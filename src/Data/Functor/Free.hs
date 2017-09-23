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

  ) where

import Control.Comonad
import Data.Function
import Data.Semigroup

import Data.Constraint hiding (Class)
import Data.Constraint.Forall
import Data.Constraint.Class1

import Data.Foldable (Foldable(..))
import Data.Traversable
import Data.Void

import Data.Algebra
import Language.Haskell.TH.Syntax

import Data.Functor.Free.TH


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

rightAdjunctF :: ForallF c f => (a -> f b) -> Free c a -> f b
rightAdjunctF = h instF rightAdjunct
  where
    h :: ForallF c f
      => (ForallF c f :- c (f b))
      -> (c (f b) => (a -> f b) -> Free c a -> f b)
      -> (a -> f b) -> Free c a -> f b
    h (Sub Dict) f = f

class ForallLifted c where
  dictLifted :: Applicative f => Dict (c (LiftAFree c f a))

rightAdjunctLifted :: (ForallLifted c, Applicative f) => (a -> LiftAFree c f b) -> Free c a -> LiftAFree c f b
rightAdjunctLifted = h dictLifted rightAdjunct
  where
    h :: Dict (c (t f b))
      -> (c (t f b) => (a -> t f b) -> Free c a -> t f b)
      -> (a -> t f b) -> Free c a -> t f b
    h Dict f = f

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

instance Functor (Free c) where
  fmap f = transform (. f)

instance Applicative (Free c) where
  pure = unit
  fs <*> as = transform (\k f -> rightAdjunct (k . f) as) fs

instance Monad (Free c) where
  return = unit
  as >>= f = transform (\k -> rightAdjunct k . f) as

newtype Extract a = Extract { getExtract :: a }
newtype Duplicate f a = Duplicate { getDuplicate :: f (f a) }
instance (ForallF c Extract, ForallF c (Duplicate (Free c)))
  => Comonad (Free c) where
  extract = getExtract . rightAdjunctF Extract
  duplicate = getDuplicate . rightAdjunctF (Duplicate . unit . unit)

instance SuperClass1 (Class f) c => Algebra f (Free c a) where
  algebra fa = Free $ \k -> h scls1 (fmap (rightAdjunct k) fa)
    where
      h :: c b => (c b :- Class f b) -> f b -> b
      h (Sub Dict) = evaluate
      



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



newtype LiftAFree c f a = LiftAFree { getLiftAFree :: f (Free c a) }

instance (Applicative f, SuperClass1 (Class s) c) => Algebra s (LiftAFree c f a) where
  algebra = LiftAFree . fmap algebra . traverse getLiftAFree

instance ForallLifted c => Foldable (Free c) where
  foldMap = foldMapDefault

instance ForallLifted c => Traversable (Free c) where
  traverse f = getLiftAFree . rightAdjunctLifted (LiftAFree . fmap unit . f)


data ShowHelper f a = ShowUnit a | ShowRec (f (ShowHelper f a))

instance Algebra f (ShowHelper f a) where
  algebra = ShowRec

instance (Show a, Show (f (ShowHelper f a))) => Show (ShowHelper f a) where
  showsPrec p (ShowUnit a) = showParen (p > 10) $ showString "unit " . showsPrec 11 a
  showsPrec p (ShowRec f) = showsPrec p f

instance (Show a, Show (Signature c (ShowHelper (Signature c) a)), c (ShowHelper (Signature c) a)) => Show (Free c a) where
  showsPrec p = showsPrec p . rightAdjunct (ShowUnit :: a -> ShowHelper (Signature c) a)
  
-- | Derive the instances of @`Free` c a@ for the class @c@, `Show`, `Foldable` and `Traversable`.
--
-- For example:
--
-- @deriveInstances ''Num@
deriveInstances :: Name -> Q [Dec]
deriveInstances = deriveInstances' ''ForallLifted 'dictLifted ''Free ''LiftAFree ''ShowHelper

deriveInstances' ''ForallLifted 'dictLifted ''Free ''LiftAFree ''ShowHelper ''Num
deriveInstances' ''ForallLifted 'dictLifted ''Free ''LiftAFree ''ShowHelper ''Semigroup
deriveInstances' ''ForallLifted 'dictLifted ''Free ''LiftAFree ''ShowHelper ''Monoid
