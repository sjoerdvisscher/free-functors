{-# LANGUAGE 
  TemplateHaskell, FlexibleInstances, UndecidableInstances, 
  TypeOperators, MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses, QuantifiedConstraints 
  #-}
  
module Sem where
  
import Data.Functor.Free

class BaseSem a where
  val :: Int -> a
  add :: a -> a -> a

instance BaseSem Int where
  val = id
  add = (+)

class SubSem a where
  sub :: a -> a -> a

instance SubSem Int where
  sub = (-)

class MulSem a where
  mul :: a -> a -> a

instance MulSem Int where
  mul = (*)


class (a x, b x) => (a + b) x
instance (a x, b x) => (a + b) x
  

deriveInstances ''BaseSem
deriveInstances ''SubSem
deriveInstances ''MulSem


test :: Free (BaseSem + SubSem + MulSem) String
test = mul (add (pure "a") (val 3)) (sub (val 5) (pure "b"))

eval :: Free (BaseSem + SubSem + MulSem) String -> Int
eval = rightAdjunct lookupVar
  where
    lookupVar :: String -> Int
    lookupVar "a" = 2
    lookupVar "b" = 1
    lookupVar v = error $ "Unknown variable: " ++ v

main :: IO ()
main = putStrLn $ show test ++ " = " ++ show (eval test)
