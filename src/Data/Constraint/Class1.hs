{-# LANGUAGE
    PolyKinds
  , DataKinds
  , RankNTypes
  , TypeFamilies
  , TypeOperators
  , ConstraintKinds
  , FlexibleContexts
  , DefaultSignatures
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , MultiParamTypeClasses
  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.HasSuperClasses
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Data.Constraint.Class1 where

import Data.Constraint
import Data.Proxy
import Prelude hiding (id, (.))

import Control.Applicative
import Control.Arrow (Arrow, ArrowZero, ArrowPlus, ArrowLoop, ArrowApply, ArrowChoice)
import Control.Category
import Control.Comonad
import Data.Biapplicative
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Profunctor

-- | Proof that @b@ is a superclass of @h@, i.e. @h x@ entails @b x@.
scls1 :: forall b h x. SuperClass1 b h => h x :- b x
scls1 = containsSelf . isSubset (Proxy :: Proxy x) (Proxy :: Proxy (SuperClasses b)) (Proxy :: Proxy (SuperClasses h)) . superClasses

type SuperClass1 b h = (HasSuperClasses h, HasSuperClasses b, SuperClasses b `Subset` SuperClasses h, IsSubset (SuperClasses b) (SuperClasses h))

class HasSuperClasses (c :: k -> Constraint) where
  type SuperClasses c :: [k -> Constraint]
  type SuperClasses c = '[c]
  superClasses :: c x :- FoldConstraints (SuperClasses c) x
  default superClasses :: c x :- FoldConstraints '[c] x
  superClasses = Sub Dict
  containsSelf :: FoldConstraints (SuperClasses c) x :- c x
  default containsSelf :: FoldConstraints '[c] x :- c x
  containsSelf = Sub Dict

instance HasSuperClasses Functor
instance HasSuperClasses Applicative where
  type SuperClasses Applicative = Applicative ': SuperClasses Functor
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses Alternative where
  type SuperClasses Alternative = Alternative ': SuperClasses Applicative
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses Monad where
  type SuperClasses Monad = Monad ': SuperClasses Applicative
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses Foldable
instance HasSuperClasses Traversable where
  type SuperClasses Traversable = Traversable ': SuperClasses Functor ++ SuperClasses Foldable
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses Comonad where
  type SuperClasses Comonad = Comonad ': SuperClasses Functor
  superClasses = Sub Dict
  containsSelf = Sub Dict

instance HasSuperClasses Contravariant
instance HasSuperClasses Divisible where
  type SuperClasses Divisible = Divisible ': SuperClasses Contravariant
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses Decidable where
  type SuperClasses Decidable = Decidable ': SuperClasses Divisible
  superClasses = Sub Dict
  containsSelf = Sub Dict

instance HasSuperClasses Category
instance HasSuperClasses Arrow where
  type SuperClasses Arrow = Arrow ': SuperClasses Category
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses ArrowZero where
  type SuperClasses ArrowZero = ArrowZero ': SuperClasses Arrow
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses ArrowPlus where
  type SuperClasses ArrowPlus = ArrowPlus ': SuperClasses ArrowZero
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses ArrowChoice where
  type SuperClasses ArrowChoice = ArrowChoice ': SuperClasses Arrow
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses ArrowApply where
  type SuperClasses ArrowApply = ArrowApply ': SuperClasses Arrow
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses ArrowLoop where
  type SuperClasses ArrowLoop = ArrowLoop ': SuperClasses Arrow
  superClasses = Sub Dict
  containsSelf = Sub Dict

instance HasSuperClasses Bifunctor
instance HasSuperClasses Biapplicative where
  type SuperClasses Biapplicative = Biapplicative ': SuperClasses Bifunctor
  superClasses = Sub Dict
  containsSelf = Sub Dict

instance HasSuperClasses Profunctor
instance HasSuperClasses Strong where
  type SuperClasses Strong = Strong ': SuperClasses Profunctor
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses Choice where
  type SuperClasses Choice = Choice ': SuperClasses Profunctor
  superClasses = Sub Dict
  containsSelf = Sub Dict
instance HasSuperClasses Closed where
  type SuperClasses Closed = Closed ': SuperClasses Profunctor
  superClasses = Sub Dict
  containsSelf = Sub Dict


type family (++) (as :: [k]) (bs :: [k]) :: [k] where
  (++) a '[] = a
  (++) '[] b = b
  (++) (a ': as) bs = a ': (as ++ bs)

type family FoldConstraints (cs :: [k -> Constraint]) (x :: k) :: Constraint
type instance FoldConstraints '[] x = ()
type instance FoldConstraints (c ': cs) x = (c x, FoldConstraints cs x)

class Elem (c :: k -> Constraint) (cs :: [k -> Constraint]) where
  isElem :: Proxy cs -> FoldConstraints cs x :- c x
instance {-# OVERLAPPING #-} Elem c (c ': cs) where
  isElem _ = weaken1
instance {-# OVERLAPPABLE #-} Elem b cs => Elem b (c ': cs) where
  isElem _ = isElem (Proxy :: Proxy cs) . weaken2

class IsSubset as bs where
  isSubset :: as `Subset` bs => Proxy x -> Proxy as -> Proxy bs -> FoldConstraints bs x :- FoldConstraints as x
instance IsSubset '[] bs where
  isSubset _ _ _ = top
instance IsSubset as bs => IsSubset (a ': as) bs where
  isSubset px _ pbs = isElem pbs &&& isSubset px (Proxy :: Proxy as) pbs

type family Subset (xs :: [k]) (ys :: [k]) :: Constraint
type instance Subset '[] bs = ()
type instance Subset (a ': as) bs = (Elem a bs, Subset as bs)
