{-# LANGUAGE FlexibleInstances #-}
module NonEmptyList where

import Data.Functor.Free

import Data.Semigroup

import Control.Applicative
import Control.Comonad
import Data.Functor.Identity
import Data.Functor.Compose


-- This declaration creates a Functor that is also Applicative.
type NonEmptyList = Free Semigroup

-- This instance makes NonEmptyList a Monad.
instance Semigroup (NonEmptyList a) where
  Free fa <> Free fb = Free $ liftA2 (<>) fa fb

-- This instance makes NonEmptyList Foldable and Traversable.
instance Applicative f => Semigroup (LiftAFree Semigroup f a) where
  LiftAFree fa <> LiftAFree fb = LiftAFree $ liftA2 (<>) fa fb

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