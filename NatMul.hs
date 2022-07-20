{-# LANGUAGE    DataKinds 
  ,             GADTs 
  ,             LambdaCase
  ,             NoStarIsType
  ,             TypeFamilies
  ,             UndecidableInstances
  #-}

module NatMul where

import Data.Type.Equality

import Nat
import NatAdd
import Ops

instance Mul Nat where
    type Z * m = Z
    type S n * m = m + n * m

    (.*.) :: SNat n -> SNat m -> SNat (n * m)
    (.*.) SZ _ = SZ
    (.*.) (SS n) m = m .+. (n .*. m)

natMulZ :: SNat n -> n * Z :~: Z
natMulZ SZ = Refl
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
    ) $                             -- m + n * S n = m + (n * m + n)
    natAddSameL m $
    trans (natMulS n m) $
    natAddComm n $ n .*. m


natAddMulDistR :: SNat n -> SNat m -> SNat k -> (n + m) * k :~: n * k + m * k
natAddMulDistR SZ _ _ = Refl
natAddMulDistR (SS n) m k =     -- k + (n + m) * k = (k + n * k) + m * k
    flip trans (
        natAddAssoc k (n .*. k) (m .*. k)
    ) $                         -- k + (n + m) * k = k + (n * k + m * k)
    natAddSameL k $
    natAddMulDistR n m k


natMulAssoc :: SNat n -> SNat m -> SNat k -> n * (m * k) :~: (n * m) * k
natMulAssoc SZ _ _ = Refl
natMulAssoc (SS n) m k =        -- m * k + n * (m * k) = (m + n * m) * k
    flip trans (
        sym $ natAddMulDistR m (n .*. m) k
    ) $                         -- m * k + n * (m * k) = m * k + (n * m) * k
    natAddSameL (m .*. k) $
    natMulAssoc n m k


natMulComm :: SNat n -> SNat m -> n * m :~: m * n
natMulComm SZ m = sym $ natMulZ m
natMulComm (SS n) m =           -- m + n * m = m * S n
    flip trans (
        sym $ natMulS m n
    ) $                         -- m + n * m = m + m * n
    natAddSameL m $
    natMulComm n m

natAddMulDistL :: SNat n -> SNat m -> SNat k -> k * (n + m) :~: k * n + k * m
natAddMulDistL n m k =
    trans (natMulComm k $ n .+. m) $
    trans (natAddMulDistR n m k) $
    natAddBothSame (natMulComm n k) (natMulComm m k)


natMulSameR :: SNat k -> forall n m. n :~: m -> n * k :~: m * k
natMulSameR _ Refl = Refl

natMulSameL :: SNat k -> forall n m. n :~: m -> k * n :~: k * m
natMulSameL _ Refl = Refl
