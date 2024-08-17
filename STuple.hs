{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
module STuple where

import           Data.Kind
import           Single

data SPair :: (a, b) -> Type where
    SPair :: Sing x -> Sing y -> SPair '(x, y)
instance (Single a, Single b) => Single (a, b) where
    type Sing p = SPair p
    type Desing (a, b) = (Desing a, Desing b)
    fromSing (SPair x y) = (fromSing x, fromSing y)
    withSing (x, y) f = withSing x $ \sx -> withSing y $ f . SPair sx


data STriple :: (a, b, c) -> Type where
    STriple :: Sing x -> Sing y -> Sing z -> STriple '(x, y, z)
instance (Single a, Single b, Single c) => Single (a, b, c) where
    type Sing p = STriple p
    type Desing (a, b, c) = (Desing a, Desing b, Desing c)
    fromSing (STriple x y z) = (fromSing x, fromSing y, fromSing z)
    withSing (x, y, z) f = withSing x $ \sx -> withSing y $ \sy -> withSing z $ f . STriple sx sy


type F_PFst = F_PFst0
data F_PFst0 :: (a, b) ~> a
type F_PFst1 p = PFst p
type family PFst (p :: (a, b)) :: a where
    PFst '(x, y) = x
type instance Apply F_PFst0 p = F_PFst1 p
f_PFst :: SFunction F_PFst
f_PFst = SFunction { applyFunc = sPFst}
sPFst :: Sing p -> Sing (PFst p)
sPFst (SPair x _) = x

type F_PSnd = F_PSnd0
data F_PSnd0 :: (a, b) ~> b
type F_PSnd1 p = PSnd p
type family PSnd (p :: (a, b)) :: b where
    PSnd '(x, y) = y
type instance Apply F_PSnd0 p = F_PSnd1 p
f_PSnd :: SFunction F_PSnd
f_PSnd = SFunction { applyFunc = sPSnd}
sPSnd :: Sing p -> Sing (PSnd p)
sPSnd (SPair _ y) = y


type F_TFst = F_TFst0
data F_TFst0 :: (a, b, c) ~> a
type F_TFst1 p = TFst p
type family TFst (p :: (a, b, c)) :: a where
    TFst '(x, y, z) = x
type instance Apply F_TFst0 p = F_TFst1 p
f_TFst :: SFunction F_TFst
f_TFst = SFunction { applyFunc = sTFst}
sTFst :: Sing p -> Sing (TFst p)
sTFst (STriple x _ _) = x

type F_TSnd = F_TSnd0
data F_TSnd0 :: (a, b, c) ~> b
type F_TSnd1 p = TSnd p
type family TSnd (p :: (a, b, c)) :: b where
    TSnd '(_, y, _) = y
type instance Apply F_TSnd0 p = F_TSnd1 p
f_TSnd :: SFunction F_TSnd
f_TSnd = SFunction { applyFunc = sTSnd}
sTSnd :: Sing p -> Sing (TSnd p)
sTSnd (STriple _ y _) = y

type F_TThd = F_TThd0
data F_TThd0 :: (a, b, c) ~> c
type F_TThd1 p = TThd p
type family TThd (p :: (a, b, c)) :: c where
    TThd '(_, _, z) = z
type instance Apply F_TThd0 p = F_TThd1 p
f_TThd :: SFunction F_TThd
f_TThd = SFunction { applyFunc = sTThd}
sTThd :: Sing p -> Sing (TThd p)
sTThd (STriple _ _ z) = z
