{-# LANGUAGE
    GADTs
  , RankNTypes
  , TypeOperators
  , DeriveFunctor
  , DeriveFoldable
  , ConstraintKinds
  , TemplateHaskell
  , DeriveTraversable
  , FlexibleInstances
  , ScopedTypeVariables
  , UndecidableInstances
  , QuantifiedConstraints
  , MultiParamTypeClasses
  , UndecidableSuperClasses
  #-}
module Data.Functor.Free.Internal where

import Control.Comonad
import Data.Algebra
import Data.Algebra.TH
import Language.Haskell.TH.Syntax
import Data.Traversable

-- | The free functor for class @c@.
--
--   @Free c a@ is basically an expression tree with operations from class @c@
--   and variables/placeholders of type @a@, created with `unit`.
--   Monadic bind allows you to replace each of these variables with another sub-expression.
newtype Free c a = Free { runFree :: forall b. c b => (a -> b) -> b }

-- | `unit` allows you to create @`Free` c@ values, together with the operations from the class @c@.
unit :: a -> Free c a
unit a = Free $ \k -> k a

-- | `rightAdjunct` is the destructor of @`Free` c@ values.
rightAdjunct :: c b => (a -> b) -> Free c a -> b
rightAdjunct f g = runFree g f

-- | @counit = rightAdjunct id@
counit :: c a => Free c a -> a
counit = rightAdjunct id

-- | @leftAdjunct f = f . unit@
leftAdjunct :: (Free c a -> b) -> a -> b
leftAdjunct f = f . unit

-- | @transform f as = as >>= f unit@
--
-- @transform f . transform g = transform (g . f)@
transform :: (forall r. c r => (b -> r) -> a -> r) -> Free c a -> Free c b
transform t (Free f) = Free (f . t)


instance Functor (Free c) where
  fmap f = transform (. f)

instance Applicative (Free c) where
  pure = unit
  fs <*> as = transform (\k f -> rightAdjunct (k . f) as) fs

instance Monad (Free c) where
  return = unit
  as >>= f = transform (\k -> rightAdjunct k . f) as

newtype Extract a = Extract { getExtract :: a }
newtype Duplicate f a = Duplicate { getDuplicate :: f (f a) }
instance (forall x. c (Extract x), forall x. c (Duplicate (Free c) x))
  => Comonad (Free c) where
  extract = getExtract . rightAdjunct Extract
  duplicate = getDuplicate . rightAdjunct (Duplicate . unit . unit)
      

class (Class f x) => Class' f x where evaluate' :: AlgebraSignature f => f x -> x
instance (Class f x) => Class' f x where evaluate' = evaluate

newtype LiftAFree c f a = LiftAFree { getLiftAFree :: f (Free c a) }

instance (forall x. c x => Class' f x) => Algebra f (Free c a) where
  algebra fa = Free $ \k -> evaluate' (fmap (rightAdjunct k) fa)
      
instance (Applicative f, forall x. c x => Class' s x) => Algebra s (LiftAFree c f a) where
  algebra = LiftAFree . fmap algebra . traverse getLiftAFree

instance (forall f x. Applicative f => c (LiftAFree c f x)) => Foldable (Free c) where
  foldMap = foldMapDefault

instance (forall f x. Applicative f => c (LiftAFree c f x)) => Traversable (Free c) where
  traverse f = getLiftAFree . rightAdjunct (LiftAFree . fmap unit . f)


data ShowHelper a where 
  ShowUnit :: a -> ShowHelper a
  ShowRec :: Show (f (ShowHelper a)) => f (ShowHelper a) -> ShowHelper a

instance Show (f (ShowHelper a)) => Algebra f (ShowHelper a) where
  algebra = ShowRec

instance Show a => Show (ShowHelper a) where
  showsPrec p (ShowUnit a) = showParen (p > 10) $ showString "unit " . showsPrec 11 a
  showsPrec p (ShowRec f) = showsPrec p f

instance (Show a, Show (Signature c (ShowHelper a)), c (ShowHelper a)) => Show (Free c a) where
  showsPrec p = showsPrec p . rightAdjunct ShowUnit


class (a => b) => a :=> b
instance (a => b) => a :=> b

-- | Derive the instances of @`Free` c a@ for the class @c@, `Show`, `Foldable` and `Traversable`.
--
-- For example:
--
-- @deriveInstances ''Num@
deriveInstances :: Name -> Q [Dec]
deriveInstances nm = 
  concat <$> sequenceA
  [ deriveSignature nm
  , deriveInstanceWith_skipSignature freeHeader $ return []
  , deriveInstanceWith_skipSignature liftAFreeHeader $ return []
  , deriveInstanceWith_skipSignature showHelperHeader $ return []
  ]
  where
    freeHeader = [t|forall a c. (forall x. c x :=> $clss x) => $clss (Free c a)|]
    liftAFreeHeader = [t|forall f a c. (Applicative f, forall x. c x :=> $clss x) => $clss (LiftAFree c f a)|]
    showHelperHeader = [t|forall a. Show a => $clss (ShowHelper a)|]
    clss = pure $ ConT nm
