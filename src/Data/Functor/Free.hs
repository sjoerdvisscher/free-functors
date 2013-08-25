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

-- | The free functor for constraint @c@.
newtype Free c a = Free { runFree :: forall b. c b => (a -> b) -> b }

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
  
unit :: a -> Free c a
unit a = Free $ \k -> k a

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

instance Functor (Free c) where
  fmap f (Free g) = Free (g . (. f))

instance Applicative (Free c) where
  pure = unit
  fs <*> as = Free $ \k -> runFree fs (\f -> runFree as (k . f))

instance ForallF c (Free c) => Monad (Free c) where
  return = unit
  (>>=) = flip rightAdjunctF

instance (ForallF c Identity, ForallF c (Free c), ForallF c (Compose (Free c) (Free c)))
  => Comonad (Free c) where
  extract = runIdentity . rightAdjunctF Identity
  extend g = fmap g . getCompose . rightAdjunctF (Compose . return . return)

instance c ~ Class f => Algebra f (Free c a) where
  algebra fa = Free $ \k -> evaluate (fmap (rightAdjunct k) fa)

newtype LiftAFree c f a = LiftAFree { getLiftAFree :: f (Free c a) }

instance (Applicative f, c ~ Class s) => Algebra s (LiftAFree c f a) where
  algebra = LiftAFree . fmap algebra . traverse getLiftAFree

instance ForallT c (LiftAFree c) => Foldable (Free c) where
  foldMap = foldMapDefault

instance ForallT c (LiftAFree c) => Traversable (Free c) where
  traverse f = getLiftAFree . rightAdjunctT (LiftAFree . fmap pure . f)

convert :: (c (f a), Applicative f) => Free c a -> f a
convert = rightAdjunct pure

convertClosed :: c r => Free c Void -> r
convertClosed = rightAdjunct absurd

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