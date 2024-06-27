{-# LANGUAGE    DataKinds 
  ,             GADTs 
  ,             LambdaCase
  ,             NoStarIsType
  ,             TypeFamilies
  #-}

module Nat where

import Data.Kind
import Data.Type.Equality

import Single

data Nat = Z | S Nat

data SNat :: Nat -> Type where
    SZ :: SNat Z
    SS :: SNat n -> SNat (S n)

type F_S = F_S0
data F_S0 :: Nat ~> Nat
type F_S1 n = S n
type instance Apply F_S0 n = F_S1 n
f_S :: SFunction F_S
f_S = SFunction { applyFunc = \n -> SS n}

instance Single Nat where
    type Sing n = SNat n
    type Desing Nat = Nat

    fromSing SZ = Z
    fromSing (SS n) = S $ fromSing n

    withSing Z f = f SZ
    withSing (S n) f = withSing n $ \n' -> f $ SS n'

instance EqDec Nat where
    SZ =?= SZ = Left Refl
    SS _ =?= SZ = Right $ \case
    SZ =?= SS _ = Right $ \case
    SS n =?= SS m = case n =?= m of
        Left eq -> Left $ apply Refl eq
        Right neq -> Right $ \eq -> neq $ inner eq

type N0 = Z
type N1 = S N0
type N2 = S N1
type N3 = S N2
type N4 = S N3
type N5 = S N4
type N6 = S N5
type N7 = S N6
type N8 = S N7
type N9 = S N8
n0 = SZ
n1 = SS n0
n2 = SS n1
n3 = SS n2
n4 = SS n3
n5 = SS n4
n6 = SS n5
n7 = SS n6
n8 = SS n7
n9 = SS n8
