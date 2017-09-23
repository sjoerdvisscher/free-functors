{-# LANGUAGE TemplateHaskell, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleInstances #-}
module FreeNum where

import Data.Functor.Free

-- This is what you would normally do with your own class, for Num this is already done for you.
-- deriveInstances ''Num


x, y :: Free Num String
x = return "x"
y = return "y"

-- try showing expr
expr :: Free Num String
expr = 1 + x * (3 - y)

-- Monadic bind is variable substitution
subst :: Free Num String -> Free Num a
subst e = e >>= \v -> case v of 
  "x" -> 10
  _   -> 2

-- Closed expressions can be evaluated to any other instance of Num
result :: Int
result = convertClosed (subst expr)