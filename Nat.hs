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
