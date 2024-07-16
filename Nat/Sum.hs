{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Nat.Sum where

import           Data.Type.Equality

import           Add
import           Mul
import           Nat.Add
import           Nat.Defs
import           Nat.Mul
import           Ops
import           PointwiseFuncOps
import           SFuncUnsafe
import           Single

type family Sum (f :: Nat ~> r) (max :: Nat) :: r where
    Sum f Z = AddZero
    Sum f (S n) = f @@ n + Sum f n

monSum :: AddMonoid k => SFunction (f :: Nat ~> k) -> SNat n -> Sing (Sum f n)
monSum _ SZ     = addZero
monSum f (SS n) = f @@ n .+. monSum f n

sumZero :: AddMonoid k => SNat n -> Sum (F_Const @@ (AddZero :: k)) n :~: AddZero
sumZero SZ     = Refl
sumZero (SS n) = trans (addZeroL $ monSum (f_Const @@ addZero) n) $ sumZero n

sumFuncApplyDist :: AddMonoid k => SNat n -> SFunction (f :: l ~> Nat ~> k) -> Sing m -> Sum (f @@ m) n :~: Sum (F_Flip @@ f) n @@ m
sumFuncApplyDist SZ _ _     = Refl
sumFuncApplyDist (SS n) f m = addSameL (f @@ m @@ n) $ sumFuncApplyDist n f m

sumEqFunc :: AddMonoid k => SNat n -> SFunction (f :: Nat ~> k) -> SFunction (g :: Nat ~> k) -> f :~: g -> Sum f n :~: Sum g n
sumEqFunc _ _ _ Refl = Refl


natSum :: SFunction f -> SNat n -> SNat (Sum f n)
natSum = monSum

natSumSame :: SNat n -> SNat m -> Sum (F_Const1 m) n :~: m * n
natSumSame SZ m = sym $ natMulZ m
natSumSame (SS n) m =       -- m + Sum (K m) n = m * S n
    flip trans (
        sym $ natMulS m n
    ) $                     -- m + Sum (K m) n = m + m * n
    natAddSameL m $
    natSumSame n m


natSumId :: SNat n -> N2 * Sum F_Id (S n) :~: n * S n
natSumId SZ = natMulZ n2
natSumId (SS (n :: SNat n)) =   -- 2 * (S n + Sum id (S n)) = S n * S S n
    trans (
        natAddMulDistL (SS n) (natSum f_Id (SS n)) n2
    ) $                         -- 2 * S n + 2*Sum id (S n) = S n * S S n
    trans (                                     -- 2 * S n + 2*Sum id (S n) = 2 * S n + n * S n
        natAddSameL (n2 .*. SS n) $            -- 2*Sum id (S n) = n * S n
        natSumId n
    ) $                         -- 2 * S n + n * S n = S n * S S n
    flip trans (
        natMulComm (SS $ SS n) $ SS n
    ) $                         -- 2 * S n + n * S n = S S n * S n
    sym $                       -- S S n * S n = 2 * S n + n * S n
    natAddMulDistR n2 n $ SS n


sumSplit :: forall k n f g. (AddComm k, AddMonoid k) => SNat n -> SFunction (f :: Nat ~> k) -> SFunction (g :: Nat ~> k) -> Sum (f + g) n :~: Sum f n + Sum g n
sumSplit SZ _ _ = sym (addZeroL addZero)
sumSplit (SS n) f g =           -- (f n + g n) + Sum (f + g) n = (f n + Sum f n) + (g n + Sum g n)
    trans (
        sym $ addAssoc (f @@ n) (g @@ n) (monSum (f .+. g) n)
    ) $                         -- f n + (g n + Sum (f + g) n) = (f n + Sum f n) + (g n + Sum g n)
    flip trans (
        addAssoc (f @@ n) (monSum f n) (g @@ n .+. monSum g n)
    ) $                         -- f n + (g n + Sum fun n) = f n + (Sum f n + (g n + Sum g n))
    addSameL (f @@ n) $      -- g n + Sum fun n = Sum f n + (g n + Sum g n)
    flip trans (
        addFlipL (g @@ n) (monSum f n) (monSum g n)
    ) $                         -- g n + Sum fun n = g n + (Sum f n + Sum g n)
    addSameL (g @@ n) $      -- Sum fun n = Sum f n + Sum g n
    sumSplit n f g


natSumMulOut :: SNat n -> SNat m -> SFunction f -> Sum (F_Compose @@ (F_Mul @@ m) @@ f) n :~: m * Sum f n
natSumMulOut SZ m _ = sym $ natMulZ m
natSumMulOut (SS n) m f =               -- m * f n + Sum _ n = m * (f n + Sum f n)
    flip trans (
        sym $ natAddMulDistL (applyFunc f n) (natSum f n) m
    ) $                                 -- m * f n + Sum _ n = m * f n + m * Sum f n
    natAddSameL (m .*. applyFunc f n) $ -- Sum _ n = m * Sum f n
    natSumMulOut n m f

natSumEqEach :: SNat n -> SFunction (f :: Nat ~> Nat) -> SFunction g -> (forall m. SNat m -> f @@ m :~: g @@ m) -> Sum f n :~: Sum g n
natSumEqEach SZ _ _ _ = Refl
natSumEqEach (SS n) f g eq =            -- f n + Sum f n = g n + Sum g n
    natAddBothSame (eq n) $ natSumEqEach n f g eq

type NatEven = F_Mul @@ N2
f_NatEven :: SFunction NatEven
f_NatEven = SFunction { applyFunc = (n2 .*.) }

natSumEven :: SNat n -> Sum NatEven (S n) :~: n * S n
natSumEven n =
    flip trans (natSumId n) $           -- Sum NatEven (S n) = 2 * Sum Id (S n)
    flip trans (
        natSumMulOut (SS n) n2 f_Id
    ) $                                 -- Sum NatEven (S n) = Sum (2*)@@Id (S n)
    let rhs :: SFunction (F_Compose @@ (F_Mul @@ N2) @@ F_Id) = SFunction {applyFunc = (n2 .*.)} in
    natSumEqEach (SS n) f_NatEven rhs $ const Refl


type NatOdd :: Nat ~> Nat
type NatOdd = F_Compose @@ F_S @@ NatEven
f_NatOdd :: SFunction NatOdd
f_NatOdd = SFunction {applyFunc = SS . (n2 .*.)}

natSumOdd :: SNat n -> Sum NatOdd n :~: n * n
natSumOdd SZ = Refl
natSumOdd (SS n) =                      -- S (n + n + 0) + Sum NatOdd n = S n + n * S n
    let isum = natSum f_NatOdd n in
    apply Refl $                        -- (n + (n + 0)) + Sum NatOdd n = n + n * S n
    trans (
        natAddSameR isum $ natAddSameL n $ natAddZ n
    ) $                                 -- (n + n) + Sum NatOdd n = n + n * S n
    trans (
        sym $ natAddAssoc n n isum
    ) $                                 -- n + (n + Sum NatOdd n) = n + n * S n
    natAddSameL n $                     -- n + Sum NatOdd n = n * S n
    flip trans (sym $ natMulS n n) $    -- n + Sum NatOdd n = n + n * n
    natAddSameL n $                     -- Sum NatOdd n = n * n
    natSumOdd n

natSumOdd' :: SNat n -> Sum NatOdd n :~: n * n
natSumOdd' (n :: SNat n) =      -- Sum NatOdd n = n * n
    let foo :: SFunction ((F_Const @@ N1) + NatEven) = SFunction {applyFunc = \i -> n1 .+. (n2 .*. i)} in
        -- onepEq :: Sum NatOdd n :~: Sum ((F_Const @@ N1) + NatEven) n = natSumEqEach n f_NatOdd foo (const Refl) in
    trans (
        natSumEqEach n f_NatOdd foo (const Refl)
    ) $                         -- Sum (K 1 + NatEven) n = n * n
    trans (
        sumSplit n (f_Const @@ n1) f_NatEven
    ) $                         -- Sum (K 1) n + Sum NatEven n = n * n
    trans (
        natAddSameR (natSum f_NatEven n) $ trans
            (natSumSame n n1)
            (natAddZ n)
    ) $                         -- n + Sum NatEven n = n * n
    case n of
        SZ    -> Refl
        SS n' -> natAddSameL n $ natSumEven n'


natDoubleSumSwap :: AddAbelMonoid k => SNat n -> SNat m -> SFunction (f :: Nat ~> Nat ~> k) -> Sum (Sum f m) n :~: Sum (Sum (F_Flip @@ f) n) m
natDoubleSumSwap SZ SZ _ = Refl
natDoubleSumSwap SZ (SS m) _ = trans (sym $ sumZero m) $ sym $ addZeroL $ monSum (f_Const @@ addZero) m
natDoubleSumSwap (SS n) SZ _ = flip trans (sumZero n) $ addZeroL $ monSum (f_Const @@ addZero) n
natDoubleSumSwap (SS n) (SS m) f =          -- (f m n + Sum f m n) + Sum (f m + Sum f m) n = (f m n + Sum (flip f) n m) + Sum (flip f n + Sum (flip f) n) m
    trans (
        sym $ addAssoc (f @@ m @@ n) (monSum f m @@ n) (monSum (f @@ m .+. monSum f m) n)
    ) $                                     -- f m n + (Sum f m n + Sum (f m + Sum f m) n) = (f m n + Sum (flip f) n m) + Sum (flip f n + Sum (flip f) n) m
    flip trans (
        addAssoc (f @@ m @@ n) (monSum (f_Flip @@ f) n @@ m) (monSum (f_Flip @@ f @@ n .+. monSum (f_Flip @@ f) n) m)
    ) $                                     -- f m n + (Sum f m n + Sum (f m + Sum f m) n) = f m n + (Sum (flip f) n m + Sum (flip f n + Sum (flip f) n) m)
    addSameL (f @@ m @@ n) $
    trans (                                 -- Sum f m n + Sum (f m + Sum f m) n = Sum (flip f) n m + Sum (flip f n + Sum (flip f) n) m
        addSameL (monSum f m @@ n) $ sumSplit n (f @@ m) (monSum f m)
    ) $                                     -- Sum f m n + (Sum (f m) n + Sum (Sum f m) n) = Sum (flip f) n m + Sum (flip f n + Sum (flip f) n) m
    trans (
        addFlipL (monSum f m @@ n) (monSum (f @@ m) n) (monSum (monSum f m) n)
    ) $                                     -- Sum (f m) n + (Sum f m n + Sum (Sum f m) n) = Sum (flip f) n m + Sum (flip f n + Sum (flip f) n) m
    addBothSameX (monSum (f @@ m) n) (monSum f m @@ n .+. monSum (monSum f m) n) (monSum (f_Flip @@ f) n @@ m) (monSum (f_Flip @@ f @@ n .+. monSum (f_Flip @@ f) n) m) (
        sumFuncApplyDist n f m
    ) $                                     -- Sum f m n + Sum (Sum f m) n = Sum (flip f n + Sum (flip f) n) m
    flip trans (
        sym $ sumSplit m (f_Flip @@ f @@ n) $ monSum (f_Flip @@ f) n
    ) $                                     -- Sum f m n + Sum (Sum f m) n = Sum (flip f n) m + Sum (Sum (flip f) n) m
    addBothSame (                               -- Sum f m n = Sum (flip f n) m
        trans (                                     -- Sum f m n = Sum (flip $ flip f) m n
            applyEqFunc n (monSum f m) (monSum (f_Flip @@ (f_Flip @@ f)) m) $   -- Sum f m = Sum (flip $ flip f) m
                sumEqFunc m f (f_Flip @@ (f_Flip @@ f)) $                       -- f = flip $ flip f
                flipTwiceSame f
        ) $ sym $ sumFuncApplyDist m (f_Flip @@ f) n
    ) $ natDoubleSumSwap n m f
