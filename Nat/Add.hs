{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Nat.Add where

import           Data.Type.Equality

import           Add
import           Nat.Defs
import           Single

instance Add Nat where
    type Z + m = m
    type S n + m = S (n + m)

    (.+.) :: SNat n -> SNat m -> SNat (n + m)
    (.+.) SZ m     = m
    (.+.) (SS n) m = SS (n .+. m)

natAddZ :: SNat n -> n + Z :~: n
natAddZ SZ     = Refl
natAddZ (SS n) = apply Refl $ natAddZ n

natAddS :: SNat n -> SNat m -> n + S m :~: S (n + m)
natAddS SZ _     = Refl
natAddS (SS n) m = apply Refl $ natAddS n m


natAddComm :: SNat n -> SNat m -> n + m :~: m + n
natAddComm SZ m = sym $ natAddZ m
natAddComm (SS n) m =   -- S n + m = m + S n
    flip trans (
        sym $ natAddS m n
    ) $                 -- S n + m = S m + n
    apply Refl $        -- n + m = m + n
    natAddComm n m

instance AddComm Nat where
    addComm = natAddComm

natAddAssoc :: SNat n -> SNat m -> SNat k -> n + (m + k) :~: (n + m) + k
natAddAssoc SZ _ _     = Refl
natAddAssoc (SS n) m k = apply Refl $ natAddAssoc n m k

instance AddMonoid Nat where
    addAssoc = natAddAssoc
    type AddZero = Z
    addZero = SZ
    addZeroL n = Refl
    addZeroR = natAddZ

natAddBothSame :: forall n m. n :~: m -> forall k l. k :~: l -> n + k :~: m + l
natAddBothSame Refl Refl = Refl

natAddSameL :: SNat k -> forall n m. k + n :~: k + m -> n :~: m
natAddSameL SZ eq     = eq
natAddSameL (SS k) eq = natAddSameL k $ inner eq

natAddSameR :: SNat k -> SNat n -> SNat m -> n + k :~: m + k -> n :~: m
natAddSameR k n m eq = natAddSameL k $ trans (addComm k n) $ trans eq $ addComm m k

natAddSameRS :: SNat k -> SNat n -> forall m. n :~: m -> n + k :~: m + k
natAddSameRS _ _ Refl = Refl

natAddFlipL :: SNat n -> SNat m -> SNat k -> n + (m + k) :~: m + (n + k)
natAddFlipL n m k =
    trans (natAddAssoc n m k) $
    flip trans (sym $ natAddAssoc m n k) $
    singApplyF (addR k) $
    natAddComm n m
