{-# LANGUAGE
    ConstraintKinds
  , GADTs
  , RankNTypes
  , TypeOperators
  , FlexibleInstances
  , MultiParamTypeClasses
  , UndecidableInstances
  , ScopedTypeVariables
  , DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  , TemplateHaskell
  , PolyKinds
  , DataKinds
  , QuantifiedConstraints
  #-}
module Data.Functor.Free.TH where

import Data.Constraint hiding (Class)
import Data.Constraint.Class1

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
      

newtype LiftAFree c f a = LiftAFree { getLiftAFree :: f (Free c a) }

instance SuperClass1 (Class f) c => Algebra f (Free c a) where
  algebra fa = Free $ \k -> h scls1 (fmap (rightAdjunct k) fa)
    where
      h :: c b => (c b :- Class f b) -> f b -> b
      h (Sub Dict) = evaluate
      
instance (Applicative f, SuperClass1 (Class s) c) => Algebra s (LiftAFree c f a) where
  algebra = LiftAFree . fmap algebra . traverse getLiftAFree

instance (forall f x. Applicative f => c (LiftAFree c f x)) => Foldable (Free c) where
  foldMap = foldMapDefault

instance (forall f x. Applicative f => c (LiftAFree c f x)) => Traversable (Free c) where
  traverse f = getLiftAFree . rightAdjunct (LiftAFree . fmap unit . f)


data ShowHelper f a = ShowUnit a | ShowRec (f (ShowHelper f a))

instance Algebra f (ShowHelper f a) where
  algebra = ShowRec

instance (Show a, Show (f (ShowHelper f a))) => Show (ShowHelper f a) where
  showsPrec p (ShowUnit a) = showParen (p > 10) $ showString "unit " . showsPrec 11 a
  showsPrec p (ShowRec f) = showsPrec p f

instance (Show a, Show (Signature c (ShowHelper (Signature c) a)), c (ShowHelper (Signature c) a)) => Show (Free c a) where
  showsPrec p = showsPrec p . rightAdjunct (ShowUnit :: a -> ShowHelper (Signature c) a)


deriveInstances' :: Bool -> Name -> Q [Dec]
deriveInstances' withHSC nm = getSignatureInfo nm >>= h where
  h sigInfo =
    concat <$> sequenceA
    [ deriveSignature nm
    , deriveInstanceWith_skipSignature freeHeader $ return []
    , deriveInstanceWith_skipSignature liftAFreeHeader $ return []
    , deriveInstanceWith_skipSignature showHelperHeader $ return []
    , deriveSuperclassInstances showHelperHeader
    , hasSuperClassesInstance
    ]
    where
      freeHeader = [t|forall a vc. SuperClass1 $c vc => $c (Free vc a)|]
      liftAFreeHeader = [t|forall f a vc. (Applicative f, SuperClass1 $c vc) => $c (LiftAFree vc f a)|]
      showHelperHeader = [t|forall a. $c (ShowHelper $sig a)|]
      hasSuperClassesInstance = if withHSC then [d|instance HasSuperClasses $c where {
        type SuperClasses $c = $c ': $scs;
        superClasses = Sub Dict;
        containsSelf = Sub Dict
      }|] else return []
      scs = foldr (\(SuperclassTH scnm _ _) q -> [t|SuperClasses $(pure (ConT scnm)) ++ $q|]) [t|'[]|] $ superclasses sigInfo
      c = pure $ ConT nm
      sig = pure . ConT $ signatureName sigInfo
