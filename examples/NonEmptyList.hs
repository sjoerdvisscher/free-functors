{-# LANGUAGE TemplateHaskell, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module NonEmptyList where

import Data.Functor.Free

import Control.Applicative
import Control.Comonad
import Data.Functor.Identity
import Data.Functor.Compose

import Data.Semigroup
  
-- A free semigroup allows you to create singletons and append them.
-- So it is a non-empty list.
type NonEmptyList = Free Semigroup

-- These instances make NonEmptyList Foldable, Traversable and a Monad.
deriveInstances ''Semigroup

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