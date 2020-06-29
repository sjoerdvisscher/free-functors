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
module Data.Functor.Cofree.Internal where

import Data.Monoid (Ap(..))

import Language.Haskell.TH.Syntax
import Data.DeriveLiftedInstances


kExp :: Q Exp
kExp = pure . VarE $ mkName "k"

kPat :: Pat
kPat = VarP $ mkName "k"

cofreeDeriv :: Name -> Derivator
cofreeDeriv cofree = idDeriv {
  cst = \e -> [| const $e $kExp |], -- Suppress "Defined but not used: ‘k’" warning
  res = \e -> [| $(pure (ConE cofree)) $kExp $e |],
  eff = \e -> [| $(pure (ConE cofree)) $kExp <$> $e |],
  inp = fmap (\vp -> ConP cofree [kPat, vp])
}

deriveCofreeInstance' :: Name -> Name -> Name -> Q [Dec]
deriveCofreeInstance' (pure . ConT -> cofree) ccofree (pure . ConT -> clss)
  = deriveInstance (cofreeDeriv ccofree)
      [t| forall a c. (c ~=> $clss) => $clss ($cofree c a) |]

class (a => b) => a :=> b
instance (a => b) => a :=> b

type a ~=> b = forall x. a x :=> b x
