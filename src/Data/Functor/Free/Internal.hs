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

import Data.Monoid (Ap(..))

import Language.Haskell.TH.Syntax
import Data.DeriveLiftedInstances


kExp :: Q Exp
kExp = pure . VarE $ mkName "k"

kPat :: Q Pat
kPat = pure . VarP $ mkName "k"

freeDeriv :: Name -> Name -> Derivator
freeDeriv free runFree = noopDeriv {
  run = \e -> [|$(pure $ ConE free) $ \ $kPat -> $e|],
  var = \v -> [|$(pure $ VarE runFree) $v $kExp|],
  over = \v -> [|fmap (\a -> $(pure $ VarE runFree) a $kExp) $v|]
}

deriveFreeInstance' :: Name -> Name -> Name -> Name -> Q [Dec]
deriveFreeInstance' tfree cfree runFree nm = deriveInstance (freeDeriv cfree runFree) [t|forall a c. (forall x. c x :=> $clss x) => $clss ($free c a)|]
  where
    clss = pure $ ConT nm
    free = pure $ ConT tfree

deriveInstances' :: Name -> Name -> Name -> Name -> Q [Dec]
deriveInstances' tfree cfree runFree nm = 
  concat <$> sequenceA 
    [ deriveFreeInstance' tfree cfree runFree nm
    , deriveInstance showDeriv [t|$clss ShowsPrec|]
    , deriveInstance apDeriv [t|forall f a c. (Applicative f, $clss a) => $clss (Ap f a)|]
    ]
  where
    clss = pure $ ConT nm

class (a => b) => a :=> b
instance (a => b) => a :=> b
