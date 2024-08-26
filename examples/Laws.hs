{-# LANGUAGE
    TypeFamilies
  , GADTs
  , LambdaCase
  , RankNTypes
  , BlockArguments
  , KindSignatures
  , ScopedTypeVariables
  , ConstraintKinds
  , FlexibleInstances
  , FlexibleContexts
  , DeriveGeneric
  , DeriveAnyClass
  , TypeApplications
  , AllowAmbiguousTypes
  , StandaloneDeriving
  , UndecidableInstances
  #-}
module Laws where

import GHC.Generics (Generic)
import Data.Functor.Free ( Free )
import qualified Data.Functor.Free as Free ( rightAdjunct, unit )
import Data.Functor.HFree ( HFree )
import qualified Data.Functor.HFree as HFree ( rightAdjunct, unit )
import Data.Kind (Type, Constraint)
import Test.QuickCheck ( quickCheck, Arbitrary(..), CoArbitrary, Gen )

import Data.Monoid (Sum)
import Control.Applicative (ZipList)

data EQ a = a :=: a deriving (Eq, Show)
infix 4 :=:

class Laws (c :: Type -> Constraint) where
  type Var c :: Type
  laws :: [EQ (Free c (Var c))]

data VAR = X | Y | Z deriving (Eq, Show, Generic, CoArbitrary)

instance Show a => Show (VAR -> a) where
  show f = unlines $ map show [(X, f X), (Y, f Y), (Z, f Z)]

x, y, z :: Free c VAR
x = Free.unit X
y = Free.unit Y
z = Free.unit Z

instance Laws Semigroup where
  type Var Semigroup = VAR
  laws = [x <> (y <> z) :=: (x <> y) <> z]

instance Laws Monoid where
  type Var Monoid = VAR
  laws =
    [ x <> mempty :=: x
    , mempty <> x :=: x
    ]

props :: forall c a. (Laws c, c a, Eq a) => (Var c -> a) -> Bool
props f = and $ (\(l :=: r) -> Free.rightAdjunct f l == Free.rightAdjunct f r) <$> laws @c

checkLaws :: forall c a. (Laws c, c a, CoArbitrary (Var c), Arbitrary a, Eq a, Show (Var c -> a)) => IO ()
checkLaws = quickCheck (props @c @a)

run :: IO ()
run = checkLaws @Semigroup @(Sum Double)


data EQ1 f a = f a :==: f a
deriving instance Eq (f a) => Eq (EQ1 f a)
deriving instance Show (f a) => Show (EQ1 f a)
infix 4 :==:

class Laws1 (c :: (Type -> Type) -> Constraint) where
  type Var1 c :: (Type -> Type)
  type Param c :: Type
  laws1 :: [EQ1 (HFree c (Var1 c)) (Param c)]

data VAR1 a where
  U :: VAR1 (Int -> Int)
  V :: VAR1 (Int -> Int)
  W :: VAR1 Int
deriving instance Eq (VAR1 a)
deriving instance Show (VAR1 a)

u :: HFree c VAR1 (Int -> Int)
u = HFree.unit U
v :: HFree c VAR1 (Int -> Int)
v = HFree.unit V
w :: HFree c VAR1 Int
w = HFree.unit W

instance Laws1 Applicative where
  type Var1 Applicative = VAR1
  type Param Applicative = Int
  laws1 =
    [ (pure id <*> w) :==: w
    , (pure (.) <*> u <*> v <*> w) :==: (u <*> (v <*> w))
    , (pure (+ 1) <*> pure 2) :==: pure 3
    , (u <*> pure 1) :==: (pure ($ 1) <*> u)
    ]

newtype Nat c f = Nat (forall a. Var1 c a -> f a)
instance (Functor f, Arbitrary (f Int), Arbitrary (f (Int -> Int))) => Arbitrary (Nat Applicative f) where
  arbitrary = do
    u' <- arbitrary :: Gen (f (Int -> Int))
    v' <- arbitrary :: Gen (f (Int -> Int))
    w' <- arbitrary :: Gen (f Int)
    pure $ Nat \case
      U -> u'
      V -> v'
      W -> w'
instance (Show (f Int), Show (f (Int -> Int))) => Show (Nat Applicative f) where
  show (Nat f) = unlines [show (U, f U), show (V, f V), show (W, f W)]

instance Show (Int -> Int) where
  show f = ".." ++ (init . tail . show) [f (-2), f (-1), f 0, f 1, f 2] ++ ".."

props1 :: forall c f. (Laws1 c, c f, Eq (f (Param c))) => Nat c f -> Bool
props1 (Nat f) = and $ (\(l :==: r) -> HFree.rightAdjunct f l == HFree.rightAdjunct f r) <$> laws1 @c

checkLaws1 :: forall c f. (Laws1 c, c f, Eq (f (Param c)), Arbitrary (Nat c f), Functor f, Show (Nat c f)) => IO ()
checkLaws1 = quickCheck (props1 @c @f)

run1 :: IO ()
run1 = checkLaws1 @Applicative @[]
