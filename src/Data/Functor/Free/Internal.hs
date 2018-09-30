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
deriveFreeInstance' tfree free runFree nm = deriveInstance (freeDeriv free runFree) [t|forall a c. (forall x. c x :=> $clss x) => $clss ($(pure $ ConT tfree) c a)|]
  where
    clss = pure $ ConT nm

deriveInstances' :: Name -> Name -> Name -> Name -> Q [Dec]
deriveInstances' tfree free runFree nm = 
  (++) <$> deriveFreeInstance' tfree free runFree nm <*> deriveInstance showDeriv [t|$clss ShowsPrec|]
  where
    clss = pure $ ConT nm

class (a => b) => a :=> b
instance (a => b) => a :=> b
