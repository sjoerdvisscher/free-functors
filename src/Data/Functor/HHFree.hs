{-# LANGUAGE
    RankNTypes
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , ScopedTypeVariables
  , UndecidableInstances
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
-- Compared to @Data.Functor.HHFree@ we have 2 two parameters.
-----------------------------------------------------------------------------
module Data.Functor.HHFree where

import Prelude hiding ((.), id)
import Data.Constraint (Dict(..), (:-)(..))
import Data.Constraint.Class1

import Control.Arrow
import Control.Category
import Data.Bifunctor (Bifunctor(bimap))
import Data.Bifunctor.Functor
import Data.Biapplicative (Biapplicative(bipure, (<<*>>)))
import Data.Profunctor
import Data.Profunctor.Monad


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


instance SuperClass1 Category c => Category (HHFree c f) where
  id = HHFree $ const (h scls1)
    where
      h :: c g => (c g :- Category g) -> g a a
      h (Sub Dict) = id
  HHFree f . HHFree g = HHFree $ \k -> h scls1 (f k) (g k)
    where
      h :: c g => (c g :- Category g) -> g b d -> g a b -> g a d
      h (Sub Dict) = (.)

instance SuperClass1 Arrow c => Arrow (HHFree c f) where
  arr f = HHFree $ const (h scls1 f)
    where
      h :: c g => (c g :- Arrow g) -> (a -> b) -> g a b
      h (Sub Dict) = arr
  HHFree f *** HHFree g = HHFree $ \k -> h scls1 (f k) (g k)
    where
      h :: c g => (c g :- Arrow g) -> g a b -> g d e -> g (a, d) (b, e)
      h (Sub Dict) = (***)

instance SuperClass1 ArrowZero c => ArrowZero (HHFree c f) where
  zeroArrow = HHFree $ const (h scls1)
    where
      h :: c g => (c g :- ArrowZero g) -> g a b
      h (Sub Dict) = zeroArrow

instance SuperClass1 ArrowPlus c => ArrowPlus (HHFree c f) where
  HHFree f <+> HHFree g = HHFree $ \k -> h scls1 (f k) (g k)
    where
      h :: c g => (c g :- ArrowPlus g) -> g a b -> g a b -> g a b
      h (Sub Dict) = (<+>)

instance SuperClass1 ArrowChoice c => ArrowChoice (HHFree c f) where
  HHFree f +++ HHFree g = HHFree $ \k -> h scls1 (f k) (g k)
    where
      h :: c g => (c g :- ArrowChoice g) -> g a b -> g d e -> g (Either a d) (Either b e)
      h (Sub Dict) = (+++)

instance SuperClass1 ArrowApply c => ArrowApply (HHFree c f) where
  app = HHFree $ h scls1
    where
      h :: c g => (c g :- ArrowApply g) -> (f :~~> g) -> g (HHFree c f a b, a) b
      h (Sub Dict) k = app . arr (first (rightAdjunct k))

instance SuperClass1 ArrowLoop c => ArrowLoop (HHFree c f) where
  loop (HHFree f) = HHFree $ \k -> h scls1 (f k)
    where
      h :: c g => (c g :- ArrowLoop g) -> g (b, d) (a, d) -> g b a
      h (Sub Dict) = loop

instance SuperClass1 Bifunctor c => Bifunctor (HHFree c f) where
  bimap p q (HHFree g) = HHFree $ \k -> h scls1 p q (g k)
    where
      h :: c g => (c g :- Bifunctor g) -> (a -> b) -> (e -> d) -> g a e -> g b d
      h (Sub Dict) = bimap

instance SuperClass1 Biapplicative c => Biapplicative (HHFree c f) where
  bipure a b = HHFree $ const (h scls1 a b)
    where
      h :: c g => (c g :- Biapplicative g) -> a -> b -> g a b
      h (Sub Dict) = bipure
  HHFree f <<*>> HHFree g = HHFree $ \k -> h scls1 (f k) (g k)
    where
      h :: c g => (c g :- Biapplicative g) -> g (a -> d) (b -> e) -> g a b -> g d e
      h (Sub Dict) = (<<*>>)

instance SuperClass1 Profunctor c => Profunctor (HHFree c f) where
  dimap p q (HHFree g) = HHFree $ \k -> h scls1 p q (g k)
    where
      h :: c g => (c g :- Profunctor g) -> (b -> a) -> (e -> d) -> g a e -> g b d
      h (Sub Dict) = dimap

instance SuperClass1 Strong c => Strong (HHFree c f) where
  first' (HHFree f) = HHFree $ \k -> h scls1 (f k)
    where
      h :: c g => (c g :- Strong g) -> g a b -> g (a, d) (b, d)
      h (Sub Dict) = first'

instance SuperClass1 Choice c => Choice (HHFree c f) where
  left' (HHFree f) = HHFree $ \k -> h scls1 (f k)
    where
      h :: c g => (c g :- Choice g) -> g a b -> g (Either a d) (Either b d)
      h (Sub Dict) = left'

instance SuperClass1 Closed c => Closed (HHFree c f) where
  closed (HHFree f) = HHFree $ \k -> h scls1 (f k)
    where
      h :: c g => (c g :- Closed g) -> g a b -> g (d -> a) (d -> b)
      h (Sub Dict) = closed
