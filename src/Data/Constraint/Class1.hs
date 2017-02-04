{-# LANGUAGE
    PolyKinds
  , RankNTypes
  , TypeOperators
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , MultiParamTypeClasses
  , FunctionalDependencies
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Class1
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Constraint.Class1 (Class1(..), SuperClass1(..)) where

import Data.Constraint

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Biapplicative
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

class Class1 b h | h -> b where
  cls1 :: h x :- b x

instance Class1 Functor Applicative where cls1 = Sub Dict
instance Class1 Applicative Alternative where cls1 = Sub Dict
instance Class1 Applicative Monad where cls1 = Sub Dict
instance Class1 Functor Traversable where cls1 = Sub Dict
instance Class1 Functor Comonad where cls1 = Sub Dict
instance Class1 Contravariant Divisible where cls1 = Sub Dict
instance Class1 Divisible Decidable where cls1 = Sub Dict

instance Class1 Category Arrow where cls1 = Sub Dict
instance Class1 Arrow ArrowZero where cls1 = Sub Dict
instance Class1 ArrowZero ArrowPlus where cls1 = Sub Dict
instance Class1 Arrow ArrowChoice where cls1 = Sub Dict
instance Class1 Arrow ArrowApply where cls1 = Sub Dict
instance Class1 Arrow ArrowLoop where cls1 = Sub Dict

instance Class1 Bifunctor Biapplicative where cls1 = Sub Dict

-- | Automatically find superclasses by searching the `Class1` instances
class SuperClass1 b h where
  scls1 :: h x :- b x

instance {-# OVERLAPPING #-} SuperClass1 b b where
  scls1 = refl

instance {-# OVERLAPPABLE #-} (SuperClass1 b c, Class1 c h) => SuperClass1 b h where
  scls1 = h where
    h :: forall x. h x :- b x
    h = trans (scls1 :: c x :- b x) (cls1 :: h x :- c x)
