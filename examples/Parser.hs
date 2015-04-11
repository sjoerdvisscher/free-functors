{-# LANGUAGE
    FlexibleInstances
  , TypeOperators
  , GADTs
  , TypeSynonymInstances
  , LambdaCase
  #-}
module Parser where

import Data.Functor.HFree

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State

data ParserF c a where
  Symbol :: c -> ParserF c c

type Parser c = HFree Alternative (ParserF c)

symbol :: c -> Parser c c
symbol = liftFree . Symbol


parseF :: Eq c => ParserF c :~> StateT [c] Maybe
parseF (Symbol c) = StateT $ \case
  (a:as) | c == a -> Just (a, as)
  _ -> Nothing

parse :: Eq c => Parser c a -> [c] -> Maybe a
parse p = fmap fst . mfilter (null . snd) . runStateT (rightAdjunct parseF p)


parenDepth :: Parser Char Int
parenDepth = maximum . (0:) <$> many (succ <$> (symbol '(' *> parenDepth <* symbol ')'))

maxDepth :: String -> Maybe Int
maxDepth = parse parenDepth
