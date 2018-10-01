{-# LANGUAGE TemplateHaskell, UndecidableInstances, QuantifiedConstraints, FlexibleInstances #-}
module Sem where
  
import Data.Functor.Free

class BaseSem a where
  val :: Int -> a
  add :: a -> a -> a

instance BaseSem Int where
  val = id
  add = (+)

class BaseSem a => AdvSem a where
  mul :: a -> a -> a

instance AdvSem Int where
  mul = (*)

deriveInstances ''BaseSem
deriveInstances ''AdvSem


test :: Free AdvSem String
test = mul (add (pure "a") (val 3)) (val 5)

evaluate :: Free AdvSem String -> Int
evaluate = rightAdjunct lookupVar
  where
    lookupVar :: String -> Int
    lookupVar "a" = 2
    lookupVar v = error $ "Unknown variable: " ++ v

main :: IO ()
main = putStrLn $ show test ++ " = " ++ show (evaluate test)

vars :: Free AdvSem a -> [a]
vars = foldMap pure