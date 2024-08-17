{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
module Nat.UnsafeSum where

import           Add
import           Data.Type.Equality
import           Mul
import           Nat.Add
import           Nat.Defs
import           Nat.Sum
import           PointwiseFuncOps
import           SFuncUnsafe
import           Single


sumFuncApplyDist :: AddMonoid k => SNat n -> SFunction (f :: l ~> Nat ~> k) -> Sing m -> Sum (f @@ m) n :~: Sum (F_Flip @@ f) n @@ m
sumFuncApplyDist SZ _ _     = Refl
sumFuncApplyDist (SS n) f m = addSameL (f @@ m @@ n) $ sumFuncApplyDist n f m



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
        singApplyF (addR $ natSum f_NatEven n) $ trans
            (natSumSame n n1)
            (natAddZ n)
    ) $                         -- n + Sum NatEven n = n * n
    case n of
        SZ    -> Refl
        SS n' -> singApplyF (addL n) $ natSumEven n'


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
