{-# LANGUAGE TemplateHaskell, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleInstances, UndecidableInstances #-}
module NonEmptyList where

import Data.Functor.Free

import Control.Comonad

-- A free semigroup allows you to create singletons and append them.
-- So it is a non-empty list.
type NonEmptyList = Free Semigroup

-- These instances make NonEmptyList a Semigroup and Show-able, Foldable and Traversable.
-- This is what you would normally do with your own class, for Semigroup this is already done for you.
-- deriveInstances ''Semigroup

-- The next two instances make NonEmptyList a Comonad.
instance Semigroup (Extract a) where
  a <> _ = a

instance Semigroup (Duplicate NonEmptyList a) where
  Duplicate l <> Duplicate r = Duplicate $ ((<> extract r) <$> l) <> r

fromList :: [a] -> NonEmptyList a
fromList = foldr1 (<>) . map pure

-- Test the comonad and foldable instances, returns [15,14,12,9,5].
test :: NonEmptyList Int
test = extend sum $ ((pure 1 <> pure 2) <> pure 3 <> pure 4) <> pure 5
