{-# LANGUAGE    DataKinds 
  ,             GADTs 
  ,             LambdaCase
  ,             NoStarIsType
  ,             TypeFamilies
  ,             UndecidableInstances
  #-}

module NatSum where

import Data.Type.Equality

import Nat
import NatAdd
import NatMul
import Ops
import Single

type instance Sum _ Z = Z
type instance Sum f (S n) = f @@ n + Sum f n

natSum :: SFunction f -> SNat n -> SNat (Sum f n)
natSum _ SZ = SZ
natSum f (SS n) = applyFunc f n .+. natSum f n

natSumSame :: SNat n -> SNat m -> Sum (F_Const1 m) n :~: m * n
natSumSame SZ m = sym $ natMulZ m
natSumSame (SS n) m =       -- m + Sum (K m) n = m * S n
    flip trans (
        sym $ natMulS m n
    ) $                     -- m + Sum (K m) n = m + m * n
    natAddSameL m $
    natSumSame n m


natSumId :: SNat n -> (S (S Z)) * Sum F_Id0 (S n) :~: n * S n
natSumId SZ = natMulZ $ SS (SS SZ)
natSumId (SS (n :: SNat n)) =   -- 2 * (S n + Sum id (S n)) = S n * S S n
    let two = SS $ SS SZ in
    trans (
        natAddMulDistL (SS n) (natSum f_Id0 (SS n)) two
    ) $                         -- 2 * S n + 2*Sum id (S n) = S n * S S n
    trans (                                     -- 2 * S n + 2*Sum id (S n) = 2 * S n + n * S n
        natAddSameL (two .*. SS n) $            -- 2*Sum id (S n) = n * S n
        natSumId n
    ) $                         -- 2 * S n + n * S n = S n * S S n
    flip trans (
        natMulComm (SS $ SS n) $ SS n
    ) $                         -- 2 * S n + n * S n = S S n * S n
    sym $                       -- S S n * S n = 2 * S n + n * S n
    natAddMulDistR two n $ SS n


natSumSplit :: SNat n -> SFunction (f :: Nat ~> Nat) -> SFunction (g :: Nat ~> Nat) -> Sum (F_SApply @@ (F_Compose @@ F_Add @@ f) @@ g) n :~: Sum f n + Sum g n
natSumSplit SZ _ _ = Refl
natSumSplit (SS n) f g =        -- (f n + g n) + Sum (\x -> f x + g x) n = (f n + Sum f n) + (g n + Sum g n)
    let fun = f_SApply @@ (f_Compose @@ f_Add @@ f) @@ g in
    trans (
        sym $ natAddAssoc (f @@ n) (g @@ n) (natSum fun n)
    ) $                         -- f n + (g n + Sum fun n) = (f n + Sum f n) + (g n + Sum g n)
    flip trans (
        natAddAssoc (f @@ n) (natSum f n) (g @@ n .+. natSum g n)
    ) $                         -- f n + (g n + Sum fun n) = f n + (Sum f n + (g n + Sum g n))
    natAddSameL (f @@ n) $      -- g n + Sum fun n = Sum f n + (g n + Sum g n)
    flip trans (
        natAddFlipL (g @@ n) (natSum f n) (natSum g n)
    ) $                         -- g n + Sum fun n = g n + (Sum f n + Sum g n)
    natAddSameL (g @@ n) $      -- Sum fun n = Sum f n + Sum g n
    natSumSplit n f g


type NatOdd :: Nat ~> Nat
type NatOdd = F_Compose @@ (F_Add0 @@ S Z) @@ (F_Mul0 @@ S (S Z))

natSumOdd :: SNat n -> Sum NatOdd n :~: n * n
natSumOdd = undefined
