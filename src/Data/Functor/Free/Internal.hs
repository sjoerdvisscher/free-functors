{-# LANGUAGE
    GADTs
  , PolyKinds
  , RankNTypes
  , ViewPatterns
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
freeDeriv (pure . ConE -> free) (pure . VarE -> runFree) = idDeriv {
  res = \e -> [| $free (\ $kPat -> $e) |],
  var = \fold v -> [| $(fold [| fmap |] [| \f -> $runFree f $kExp |]) $v |]
}

deriveFreeInstance' :: Name -> Name -> Name -> Name -> Q [Dec]
deriveFreeInstance' (pure . ConT -> free) cfree runFree (pure . ConT -> clss)
  = deriveInstance
      (freeDeriv cfree runFree)
      [t| forall a c. (c ~=> $clss) => $clss ($free c a) |]

deriveInstances' :: Name -> Name -> Name -> Name -> Q [Dec]
deriveInstances' tfree cfree runFree nm@(pure . ConT -> clss) =
  concat <$> sequenceA
    [ deriveFreeInstance' tfree cfree runFree nm
    , deriveInstance showDeriv [t| $clss ShowsPrec |]
    , deriveInstance (apDeriv idDeriv) [t| forall f a c. (Applicative f, $clss a) => $clss (Ap f a) |]
    ]

class (a => b) => a :=> b
instance (a => b) => a :=> b

type a ~=> b = forall x. a x :=> b x
