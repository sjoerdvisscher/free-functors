{-# LANGUAGE
    MultiParamTypeClasses
  , FlexibleInstances
  #-}
module Automaton where

import Data.Functor.Cofree

import Control.Comonad
import Data.Functor.Identity
import Data.Functor.Compose


class Action i s where
  act :: i -> s -> s

type Automaton i = Cofree (Action i)


instance Action i (Automaton i o) where
  act i (Cofree k s) = Cofree k (act i s)

instance Action i (Identity a) where
  act _ = id

instance Action i (Compose (Automaton i) (Automaton i) o) where
  act i = Compose . fmap (act i) . act i . getCompose


data ActionD i s = ActionD (i -> s -> s) s
instance Action i (ActionD i s) where
  act i (ActionD f s) = ActionD f (f i s)

unfoldAutomaton :: (i -> s -> s) -> (s -> o) -> s -> Automaton i o
unfoldAutomaton fi fo = Cofree (\(ActionD _ s) -> fo s) . ActionD fi


type Stream = Automaton ()

unfoldStream :: (s -> (a, s)) -> s -> Stream a
unfoldStream f = unfoldAutomaton (const (snd . f)) (fst . f)

headS :: Stream a -> a
headS = extract

tailS :: Stream a -> Stream a
tailS = act ()

zipWithS :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f as bs = f <$> as <*> bs

fromStream :: Stream a -> [a]
fromStream = map headS . iterate tailS
