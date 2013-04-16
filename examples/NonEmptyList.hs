{-# LANGUAGE FlexibleInstances, TemplateHaskell, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module NonEmptyList where

import Data.Functor.Free
import Data.Algebra

import Control.Applicative
import Control.Comonad
import Data.Functor.Identity
import Data.Functor.Compose

class Semigroup s where
  (<>) :: s -> s -> s

instance Semigroup [a] where
  (<>) = (++)
  
-- This declaration creates a Functor that is also Applicative.
type NonEmptyList = Free Semigroup

-- This instance makes NonEmptyList a Monad.
deriveInstance [t| () => Semigroup (NonEmptyList a) |]

-- This instance makes NonEmptyList Foldable and Traversable.
deriveInstance [t| Applicative f => Semigroup (LiftAFree Semigroup f a) |]

-- The next two instances make NonEmptyList a Comonad.
instance Semigroup (Identity a) where
  a <> _ = a

instance Semigroup (Compose NonEmptyList NonEmptyList a) where
  Compose l <> Compose r = Compose $ ((<> extract r) <$> l) <> r

  
  
fromList :: [a] -> NonEmptyList a
fromList = foldr1 (<>) . map return

toList :: NonEmptyList a -> [a]
toList = convert


-- Test the comonad instance, returns [10,9,7,4].
test :: [Int]
test = toList $ extend (sum . toList) $ (pure 1 <> pure 2) <> (pure 3 <> pure 4)