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
module Data.Functor.Free where
  
import Control.Applicative
import Control.Comonad
import Data.Function

import Data.Constraint hiding (Class)
import Data.Constraint.Forall

import Data.Functor.Identity
import Data.Functor.Compose
import Data.Foldable (Foldable(..))
import Data.Traversable
import Data.Void

import Data.Algebra
import Data.Algebra.TH
import Language.Haskell.TH.Syntax

-- | The free functor for class @c@. 
--
--   @Free c a@ is basically an expression tree with operations from class @c@ 
--   and variables/placeholders of type @a@, created with `unit`.
--   Monadic bind allows you to replace each of these variables with another sub-expression.
newtype Free c a = Free { runFree :: forall b. c b => (a -> b) -> b }

-- | Derive the instances for the class @c@ of @`Free` c a@ and @`LiftAFree` c f a@.
--
-- For example: 
-- 
-- @deriveInstances ''Num@
deriveInstances :: Name -> Q [Dec]
deriveInstances nm = concat <$> sequenceA
  [ deriveSignature nm
  , deriveInstanceWith_skipSignature freeHeader $ return []
  , deriveInstanceWith_skipSignature liftAFreeHeader $ return []
  ]
  where
    freeHeader = return $ ForallT [PlainTV a] [] 
      (AppT c (AppT (AppT free c) (VarT a)))
    liftAFreeHeader = return $ ForallT [PlainTV f,PlainTV a] [ClassP ''Applicative [VarT f]] 
      (AppT c (AppT (AppT (AppT liftAFree c) (VarT f)) (VarT a)))
    free = ConT ''Free
    liftAFree = ConT ''LiftAFree
    c = ConT nm
    a = mkName "a"
    f = mkName "f"
  
-- | `unit` allows you to create `Free c` values, together with the operations from the class @c@.
unit :: a -> Free c a
unit a = Free $ \k -> k a

-- | `rightAdjunct` is the destructor of `Free c` values.
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

rightAdjunctT :: ForallT c t => (a -> t f b) -> Free c a -> t f b
rightAdjunctT = h instT rightAdjunct
  where
    h :: ForallT c t
      => (ForallT c t :- c (t f b))
      -> (c (t f b) => (a -> t f b) -> Free c a -> t f b)
      -> (a -> t f b) -> Free c a -> t f b
    h (Sub Dict) f = f

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

instance (ForallF c Identity, ForallF c (Compose (Free c) (Free c)))
  => Comonad (Free c) where
  extract = runIdentity . rightAdjunctF Identity
  duplicate = getCompose . rightAdjunctF (Compose . unit . unit)

instance c ~ Class f => Algebra f (Free c a) where
  algebra fa = Free $ \k -> evaluate (fmap (rightAdjunct k) fa)

newtype LiftAFree c f a = LiftAFree { getLiftAFree :: f (Free c a) }

instance (Applicative f, c ~ Class s) => Algebra s (LiftAFree c f a) where
  algebra = LiftAFree . fmap algebra . traverse getLiftAFree

instance ForallT c (LiftAFree c) => Foldable (Free c) where
  foldMap = foldMapDefault

instance ForallT c (LiftAFree c) => Traversable (Free c) where
  traverse f = getLiftAFree . rightAdjunctT (LiftAFree . fmap unit . f)



-- * Coproducts

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