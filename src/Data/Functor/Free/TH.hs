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
  #-}
module Data.Functor.Free.TH where

import Data.Constraint hiding (Class)
import Data.Constraint.Class1

import Data.Algebra.TH
import Language.Haskell.TH.Syntax

deriveInstances' :: Name -> Name -> Name -> Name -> Name -> Name -> Q [Dec]
deriveInstances' forallLiftedNm dictLiftedNm freeNm liftAFreeNm showHelperNm nm = concat <$> sequenceA
  [ deriveSignature nm
  , deriveInstanceWith_skipSignature freeHeader $ return []
  , deriveInstanceWith_skipSignature liftAFreeHeader $ return []
  , deriveInstanceWith_skipSignature showHelperHeader $ return []
  , return $ [InstanceD Nothing [] (AppT (ConT forallLiftedNm) c) [ValD (VarP dictLiftedNm) (NormalB (ConE 'Dict)) []]]
  ]
  where
    freeHeader = return $ ForallT [PlainTV a, PlainTV vc] [AppT (AppT superClass1 c) (VarT vc)]
      (AppT c (AppT (AppT free (VarT vc)) (VarT a)))
    liftAFreeHeader = return $ ForallT [PlainTV f, PlainTV a, PlainTV vc] [AppT (ConT ''Applicative) (VarT f), isSC]
      (AppT c (AppT (AppT (AppT liftAFree (VarT vc)) (VarT f)) (VarT a)))
    showHelperHeader = return $ ForallT [PlainTV a] []
      (AppT c (AppT (AppT showHelper sig) (VarT a)))
    isSC = AppT (AppT superClass1 c) (VarT vc)
    free = ConT freeNm
    liftAFree = ConT liftAFreeNm
    showHelper = ConT showHelperNm
    superClass1 = ConT ''SuperClass1
    c = ConT nm
    sig = ConT $ mkName (nameBase nm ++ "Signature")
    a = mkName "a"
    f = mkName "f"
    vc = mkName "c"

