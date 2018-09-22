{-# LANGUAGE
    RankNTypes
  , TypeOperators
  , ConstraintKinds
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
import qualified Data.Bifunctor as B (Bifunctor(..))
import Data.Bifunctor.Functor
import Data.Biapplicative (Biapplicative(..))
import Data.Profunctor
import Data.Profunctor.Unsafe
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


instance (forall x. c x => Category x) => Category (HHFree c f) where
  id = HHFree $ const id
  HHFree f . HHFree g = HHFree $ \k -> f k . g k

instance (forall x. c x => Arrow x) => Arrow (HHFree c f) where
  arr f = HHFree $ const (arr f)
  first (HHFree f) = HHFree $ \k -> first (f k)
  second (HHFree f) = HHFree $ \k -> second (f k)
  HHFree f *** HHFree g = HHFree $ \k -> f k *** g k
  HHFree f &&& HHFree g = HHFree $ \k -> f k &&& g k

instance (forall x. c x => ArrowZero x) => ArrowZero (HHFree c f) where
  zeroArrow = HHFree $ const zeroArrow

instance (forall x. c x => ArrowPlus x) => ArrowPlus (HHFree c f) where
  HHFree f <+> HHFree g = HHFree $ \k -> f k <+> g k

instance (forall x. c x => ArrowChoice x) => ArrowChoice (HHFree c f) where
  left (HHFree f) = HHFree $ \k -> left (f k)
  right (HHFree f) = HHFree $ \k -> right (f k)
  HHFree f +++ HHFree g = HHFree $ \k -> f k +++ g k
  HHFree f ||| HHFree g = HHFree $ \k -> f k ||| g k

instance (forall x. c x => ArrowApply x) => ArrowApply (HHFree c f) where
  app = HHFree $ \k -> app . arr (first (rightAdjunct k))

instance (forall x. c x => ArrowLoop x) => ArrowLoop (HHFree c f) where
  loop (HHFree f) = HHFree $ \k -> loop (f k)

instance (forall x. c x => Bifunctor x) => Bifunctor (HHFree c f) where
  first f (HHFree g) = HHFree $ \k -> B.first f (g k)
  second f (HHFree g) = HHFree $ \k -> B.second f (g k)
  bimap p q (HHFree g) = HHFree $ \k -> B.bimap p q (g k)

instance (forall x. c x => Biapplicative x) => Biapplicative (HHFree c f) where
  bipure a b = HHFree $ const (bipure a b)
  HHFree f <<*>> HHFree g = HHFree $ \k -> f k <<*>> g k
  HHFree f *>> HHFree g = HHFree $ \k -> f k *>> g k
  HHFree f <<* HHFree g = HHFree $ \k -> f k <<* g k
  biliftA2 p q (HHFree g) (HHFree h) = HHFree $ \k -> biliftA2 p q (g k) (h k)

instance (forall x. c x => Profunctor x) => Profunctor (HHFree c f) where
  lmap f (HHFree g) = HHFree $ \k -> lmap f (g k)
  rmap f (HHFree g) = HHFree $ \k -> rmap f (g k)
  f #. HHFree g = HHFree $ \k -> f #. g k
  HHFree g .# f = HHFree $ \k -> g k .# f
  dimap p q (HHFree g) = HHFree $ \k -> dimap p q (g k)

instance (forall x. c x => Strong x) => Strong (HHFree c f) where
  first' (HHFree f) = HHFree $ \k -> first' (f k)
  second' (HHFree f) = HHFree $ \k -> second' (f k)

instance (forall x. c x => Choice x) => Choice (HHFree c f) where
  left' (HHFree f) = HHFree $ \k -> left' (f k)
  right' (HHFree f) = HHFree $ \k -> right' (f k)

instance (forall x. c x => Closed x) => Closed (HHFree c f) where
  closed (HHFree f) = HHFree $ \k -> closed (f k)
