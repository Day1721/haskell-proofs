{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Int where

import           Data.Kind
import           Data.Type.Equality
import           Nat
import           Prelude            hiding (Int)
import           Single

data Int = IZ | IPos Nat | INeg Nat

data SInt :: Int -> Type where
    SIZ :: SInt IZ
    SIPos :: SNat n -> SInt (IPos n)
    SINeg :: SNat n -> SInt (INeg n)

instance Single Int where
    type Sing n = SInt n
    type Desing Int = Int

    fromSing SIZ       = IZ
    fromSing (SIPos n) = IPos $ fromSing n
    fromSing (SINeg n) = INeg $ fromSing n

    withSing IZ f       = f SIZ
    withSing (IPos n) f = withSing n $ f . SIPos
    withSing (INeg n) f = withSing n $ f . SINeg

instance EqDec Int where
    SIZ =?= SIZ     = Left Refl
    SIPos n =?= SIPos m = case (=?=) @Nat n m of
        Left Refl -> Left Refl
        Right neq -> Right $ \eq -> neq $ inner eq
    SINeg n =?= SINeg m = case (=?=) @Nat n m of
        Left Refl -> Left Refl
        Right neq -> Right $ \eq -> neq $ inner eq
    _ =?= _ = Right $ \case

type F_ZS = F_ZS0
data F_ZS0 :: Int ~> Int
type family F_ZS1 (i :: Int) where
    F_ZS1 IZ = IPos Z
    F_ZS1 (IPos n) = IPos (S n)
    F_ZS1 (INeg Z) = IZ
    F_ZS1 (INeg (S n)) = INeg n
type instance Apply F_ZS0 n = F_ZS1 n
f_ZS :: SFunction F_ZS
f_ZS = SFunction {applyFunc = \case
    SIZ -> SIPos SZ
    SIPos n -> SIPos (SS n)
    SINeg SZ -> SIZ
    SINeg (SS n) -> SINeg n
}


type F_ZP = F_ZP0
data F_ZP0 :: Int ~> Int
type family F_ZP1 (i :: Int) where
    F_ZP1 IZ = INeg Z
    F_ZP1 (IPos Z) = IZ
    F_ZP1 (IPos (S n)) = IPos n
    F_ZP1 (INeg n) = INeg (S n)
type instance Apply F_ZP0 n = F_ZP1 n
f_ZP :: SFunction F_ZP
f_ZP = SFunction {applyFunc = \case
    SIZ -> SINeg SZ
    SIPos SZ -> SIZ
    SIPos (SS n) -> SIPos n
    SINeg n -> SINeg (SS n)
}

intPSId :: SInt i -> F_ZP @@ (F_ZS @@ i) :~: i
intPSId = \case
    SIZ -> Refl
    SINeg SZ -> Refl
    SINeg (SS _) -> Refl
    SIPos _ -> Refl

intSPId :: SInt i -> F_ZS @@ (F_ZP @@ i) :~: i
intSPId = \case
    SIZ -> Refl
    SIPos SZ -> Refl
    SIPos (SS _) -> Refl
    SINeg _ -> Refl

type family N2I (n :: Nat) :: Int where
    N2I Z = IZ
    N2I (S n) = IPos n
nat2Int :: SNat n -> SInt (N2I n)
nat2Int SZ     = SIZ
nat2Int (SS n) = SIPos n

type F_N2I = F_N2I0
data F_N2I0 :: Nat ~> Int
type F_N2I1 n = N2I n
type instance Apply F_N2I0 n = F_N2I1 n
f_N2I :: SFunction F_N2I
f_N2I = SFunction {applyFunc = nat2Int}


-- type family Abs (n :: Int) :: Nat where
--     Abs IZ = Z
--     Abs (IPos n) = S n
--     Abs (INeg n) = S n

type Z0 = IZ
type Z1 = IPos N0
type Z2 = IPos N1
type Z3 = IPos N2
type Z4 = IPos N3
type ZM1 = INeg N0
type ZM2 = INeg N1
type ZM3 = INeg N2
type ZM4 = INeg N3
