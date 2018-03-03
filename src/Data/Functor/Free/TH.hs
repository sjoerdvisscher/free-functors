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
  #-}
module Data.Functor.Free.TH where

import Data.Constraint hiding (Class)
import Data.Constraint.Class1

import Data.Algebra.TH
import Language.Haskell.TH.Syntax

deriveInstances' :: Bool -> Name -> Name -> Name -> Name -> Name -> Name -> Q [Dec]
deriveInstances' withHSC forallLiftedNm dictLiftedNm freeNm liftAFreeNm showHelperNm nm = getSignatureInfo nm >>= h where
  h sigInfo =
    concat <$> sequenceA
    [ deriveSignature nm
    , deriveInstanceWith_skipSignature freeHeader $ return []
    , deriveInstanceWith_skipSignature liftAFreeHeader $ return []
    , deriveInstanceWith_skipSignature showHelperHeader $ return []
    , deriveSuperclassInstances showHelperHeader
    , hasSuperClassesInstance
    , return $ [InstanceD Nothing [] (AppT (ConT forallLiftedNm) c) [ValD (VarP dictLiftedNm) (NormalB (ConE 'Dict)) []]]
    ]
    where
      freeHeader = return $ ForallT [PlainTV a, PlainTV vc] [AppT (AppT superClass1 c) (VarT vc)]
        (AppT c (AppT (AppT free (VarT vc)) (VarT a)))
      liftAFreeHeader = return $ ForallT [PlainTV f, PlainTV a, PlainTV vc] [AppT (ConT ''Applicative) (VarT f), isSC]
        (AppT c (AppT (AppT (AppT liftAFree (VarT vc)) (VarT f)) (VarT a)))
      showHelperHeader = return $ ForallT [PlainTV a] []
        (AppT c (AppT (AppT showHelper sig) (VarT a)))
      hasSuperClassesInstance = if withHSC then [d|instance HasSuperClasses $(pure c) where {
        type SuperClasses $(pure c) = $(pure c) ': $(scs);
        superClasses = Sub Dict;
        containsSelf = Sub Dict
      }|] else return []
      scs = foldr (\(SuperclassTH scnm _ _) q -> [t|SuperClasses $(pure (ConT scnm)) ++ $(q)|]) [t|'[]|] $ superclasses sigInfo
      isSC = AppT (AppT superClass1 c) (VarT vc)
      free = ConT freeNm
      liftAFree = ConT liftAFreeNm
      showHelper = ConT showHelperNm
      superClass1 = ConT ''SuperClass1
      c = ConT nm
      sig = ConT $ signatureName sigInfo
      a = mkName "a"
      f = mkName "f"
      vc = mkName "c"
