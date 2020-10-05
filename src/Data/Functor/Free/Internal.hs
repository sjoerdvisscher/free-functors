{-# LANGUAGE
    CPP
  , GADTs
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
#if __GLASGOW_HASKELL__ >= 810
{-# LANGUAGE StandaloneKindSignatures #-}
#endif
module Data.Functor.Free.Internal where

import Data.Monoid (Ap(..))

import Language.Haskell.TH.Syntax
import Data.DeriveLiftedInstances
import Data.Kind (Constraint)


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
      [t| forall a c. (c ~=> $clss, c ($free c a)) => $clss ($free c a) |]

deriveInstances' :: Name -> Name -> Name -> Name -> Q [Dec]
deriveInstances' tfree cfree runFree nm@(pure . ConT -> clss) =
  concat <$> sequenceA
    [ deriveFreeInstance' tfree cfree runFree nm
    , deriveInstance showDeriv [t| $clss ShowsPrec |]
    , deriveInstance (apDeriv idDeriv) [t| forall f a c. (Applicative f, $clss a) => $clss (Ap f a) |]
    ]

#if __GLASGOW_HASKELL__ < 810
type a ~=> b = (forall x. (a :: (k -> Constraint)) x => (b :: (k -> Constraint)) x) :: Constraint
#else
type (~=>) :: (k -> Constraint) -> (k -> Constraint) -> Constraint
type a ~=> b = forall x. a x => b x
#endif