{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Nat.Mul where

import           Data.Type.Equality

import           Add
import           Mul
import           Nat.Add
import           Nat.Defs
import           Single

instance Mul Nat where
    type Z * m = Z
    type S n * m = m + n * m

    (.*.) :: SNat n -> SNat m -> SNat (n * m)
    (.*.) SZ _     = SZ
    (.*.) (SS n) m = m .+. (n .*. m)

natMulZ :: SNat n -> n * Z :~: Z
natMulZ SZ     = Refl
natMulZ (SS n) = natMulZ n

natMulS :: SNat n -> SNat m -> n * S m :~: n + n * m
natMulS SZ _ = Refl
natMulS (SS n) m =                  -- S m + n * S m = S n + (m + n * m)
    apply Refl $                    -- m + n * S m = n + (m + n * m)
    flip trans (
        sym $ natAddComm n $ SS n .*. m
    ) $                             -- m + n * S m = (m + n * m) + n
    flip trans (
        natAddAssoc m (n .*. m) n
    ) $                             -- m + n * S m = m + (n * m + n)
    singApplyF (f_Add @@ m) $       -- n * S m = n * m + n
    trans (natMulS n m) $
    natAddComm n $ n .*. m


natAddMulDistR :: SNat n -> SNat m -> SNat k -> (n + m) * k :~: n * k + m * k
natAddMulDistR SZ _ _ = Refl
natAddMulDistR (SS n) m k =     -- k + (n + m) * k = (k + n * k) + m * k
    flip trans (
        natAddAssoc k (n .*. k) (m .*. k)
    ) $                         -- k + (n + m) * k = k + (n * k + m * k)
    singApplyF (f_Add @@ k) $
    natAddMulDistR n m k


natMulAssoc :: SNat n -> SNat m -> SNat k -> n * (m * k) :~: (n * m) * k
natMulAssoc SZ _ _ = Refl
natMulAssoc (SS n) m k =        -- m * k + n * (m * k) = (m + n * m) * k
    flip trans (
        sym $ natAddMulDistR m (n .*. m) k
    ) $                         -- m * k + n * (m * k) = m * k + (n * m) * k
    singApplyF (f_Add @@ (m .*. k)) $
    natMulAssoc n m k

instance MulMonoid Nat where
    mulAssoc = natMulAssoc
    type MulOne = N1
    mulOneL = addZeroR
    mulOneR n = trans (natMulS n SZ) $ gcastWith (natMulZ n) $ natAddZ n


natMulComm :: SNat n -> SNat m -> n * m :~: m * n
natMulComm SZ m = sym $ natMulZ m
natMulComm (SS n) m =           -- m + n * m = m * S n
    flip trans (
        sym $ natMulS m n
    ) $                         -- m + n * m = m + m * n
    singApplyF (f_Add @@ m) $
    natMulComm n m

instance MulComm Nat where
    mulComm = natMulComm

natAddMulDistL :: SNat n -> SNat m -> SNat k -> k * (n + m) :~: k * n + k * m
natAddMulDistL n m k =
    trans (natMulComm k $ n .+. m) $
    trans (natAddMulDistR n m k) $
    natAddBothSame (natMulComm n k) (natMulComm m k)


natMulIsZ :: SNat n -> SNat m -> n * m :~: Z -> Either (n :~: Z) (m :~: Z)
natMulIsZ SZ _ _           = Left Refl
natMulIsZ _ SZ _           = Right Refl
natMulIsZ (SS n) (SS m) eq = case eq of {}

natMulIs1 :: SNat n -> SNat m -> n * m :~: N1 -> (n :~: N1, m :~: N1)
natMulIs1 SZ _ eq                   = case eq of {}
natMulIs1 n SZ eq                   = case trans (sym $ natMulZ n) eq of {}
natMulIs1 (SS SZ) (SS SZ) _         = (Refl, Refl)
natMulIs1 (SS _) (SS (SS _)) eq     = case eq of {}
natMulIs1 n@(SS (SS _)) m@(SS _) eq = case trans (mulComm m n) eq of {}
