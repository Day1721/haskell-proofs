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
import           Nat.Ord
import           Nat.Sub            hiding (type (-), (.-.))
import qualified Nat.Sub
import           Ord
import           Single

type family Sum (f :: Nat ~> r) (max :: Nat) :: r where
    Sum f Z = AddZero
    Sum f (S n) = f @@ n + Sum f n

monSum :: AddMonoid k => SFunction (f :: Nat ~> k) -> SNat n -> Sing (Sum f n)
monSum _ SZ     = addZero
monSum f (SS n) = f @@ n .+. monSum f n

type SumSE (f :: Nat ~> r) (start :: Nat) (end :: Nat) = Sum (f <@> (F_Add @@ start)) (NatSub end start)

monSumSE :: AddMonoid k => SFunction (f :: Nat ~> k) -> SNat s -> SNat e -> Sing (SumSE f s e)
monSumSE f s e = monSum (f <@> addL s) $ natSub e s

monSumSESafe :: AddMonoid k => SFunction (f :: Nat ~> k) -> SNat s -> SNat e -> s <= e -> Sing (SumSE f s e)
monSumSESafe f s e _ = monSumSE f s e


sumZero :: AddMonoid k => SNat n -> Sum (F_K (AddZero :: k)) n :~: AddZero
sumZero SZ     = Refl
sumZero (SS n) = trans (addZeroL $ monSum (f_Const @@ addZero) n) $ sumZero n

sumEqFunc :: AddMonoid k => SNat n -> SFunction (f :: Nat ~> k) -> SFunction (g :: Nat ~> k) -> f :~: g -> Sum f n :~: Sum g n
sumEqFunc _ _ _ Refl = Refl

sumEqEach :: AddMonoid k => SNat n -> SFunction (f :: Nat ~> k) -> SFunction g -> (forall k. SNat k -> k <= n -> f @@ k :~: g @@ k) -> Sum f n :~: Sum g n
sumEqEach SZ f g eq     = Refl
sumEqEach (SS n) f g eq = natAddBothSame (eq n $ NatLeS NatLeZ) $ sumEqEach n f g $ \k -> eq k . NatLeS

natSum :: SFunction f -> SNat n -> SNat (Sum f n)
natSum = monSum

natSumIdxLe :: SNat n -> SNat m -> SFunction (f :: Nat ~> Nat) -> n <= m -> Sum f n <= Sum f m
natSumIdxLe _ _ f NatLeZ           = NatLeZ
natSumIdxLe n (SS m) f (NatLeS le) = natLeTrans (natSumIdxLe n m f le) $ natNLeNplusKL (monSum f m) (f @@ m)

natSumSame :: SNat n -> SNat m -> Sum (F_K m) n :~: m * n
natSumSame SZ m = sym $ natMulZ m
natSumSame (SS n) m =       -- m + Sum (K m) n = m * S n
    flip trans (
        sym $ natMulS m n
    ) $                     -- m + Sum (K m) n = m + m * n
    singApplyF (addL m) $
    natSumSame n m


natSumId :: SNat n -> N2 * Sum F_Id (S n) :~: n * S n
natSumId SZ = natMulZ n2
natSumId (SS (n :: SNat n)) =   -- 2 * (S n + Sum id (S n)) = S n * S S n
    trans (
        addMulDistL (SS n) (natSum f_Id (SS n)) n2
    ) $                         -- 2 * S n + 2*Sum id (S n) = S n * S S n
    trans (                                 -- 2 * S n + 2*Sum id (S n) = 2 * S n + n * S n
        singApplyF (addL $ n2 .*. SS n) $   -- 2*Sum id (S n) = n * S n
        natSumId n
    ) $                         -- 2 * S n + n * S n = S n * S S n
    flip trans (
        natMulComm (SS $ SS n) $ SS n
    ) $                         -- 2 * S n + n * S n = S S n * S n
    sym $                       -- S S n * S n = 2 * S n + n * S n
    natAddMulDistR n2 n $ SS n


natSumMulOut :: SNat n -> SNat m -> SFunction f -> Sum ((F_Mul @@ m) <@> f) n :~: m * Sum f n
natSumMulOut SZ m _ = sym $ natMulZ m
natSumMulOut (SS n) m f =                           -- m * f n + Sum _ n = m * (f n + Sum f n)
    flip trans (
        sym $ addMulDistL (applyFunc f n) (natSum f n) m
    ) $                                         -- m * f n + Sum _ n = m * f n + m * Sum f n
    singApplyF (addL $ m .*. applyFunc f n) $   -- Sum _ n = m * Sum f n
    natSumMulOut n m f

natSumEqEach :: SNat n -> SFunction (f :: Nat ~> Nat) -> SFunction g -> (forall m. SNat m -> f @@ m :~: g @@ m) -> Sum f n :~: Sum g n
natSumEqEach SZ _ _ _ = Refl
natSumEqEach (SS n) f g eq =            -- f n + Sum f n = g n + Sum g n
    natAddBothSame (eq n) $ natSumEqEach n f g eq

type NatEven = F_Mul @@ N2
f_NatEven :: SFunction NatEven
f_NatEven = f_Mul @@ n2

natSumEven :: SNat n -> Sum NatEven (S n) :~: n * S n
natSumEven n =
    flip trans (natSumId n) $           -- Sum NatEven (S n) = 2 * Sum Id (S n)
    flip trans (
        natSumMulOut (SS n) n2 f_Id
    ) $                                 -- Sum NatEven (S n) = Sum (2*)@@Id (S n)
    let rhs :: SFunction ((F_Mul @@ N2) <@> F_Id) = SFunction {applyFunc = (n2 .*.)} in
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
    trans (                                 -- (n + (n + 0)) + Sum NatOdd n = (n + n) + Sum NatOdd n
        singApplyF (addR isum) $            -- n + (n + 0) = n + n
        singApplyF (addL n) $ addZeroR n
    ) $                                 -- (n + n) + Sum NatOdd n = n + n * S n
    trans (
        sym $ natAddAssoc n n isum
    ) $                                 -- n + (n + Sum NatOdd n) = n + n * S n
    singApplyF (addL n) $               -- n + Sum NatOdd n = n * S n
    flip trans (sym $ natMulS n n) $    -- n + Sum NatOdd n = n + n * n
    singApplyF (addL n) $               -- Sum NatOdd n = n * n
    natSumOdd n


sumSESplitG :: AddGroup k => SFunction (f :: Nat ~> k) -> SNat s -> SNat e -> s <= e -> SumSE f s e :~: Sum f e - Sum f s
sumSESplitG f s e NatLeZ           = sym $ gcastWith (natSubNZ s) $ addInvZR $ monSum f s
sumSESplitG f s (SS e) (NatLeS le) =     -- sum (f . (s+)) (S e - s) = (f e + sum f e) - sum f s
    gcastWith (natSubSL e s le) $       -- f (s+(e-s)) + sum (f . (s+)) (e - s) = (f e + sum f e) - sum f s
    gcastWith (natSubSplit e s le) $    -- f e + sum (f . (s+)) (e - s) = (f e + sum f e) - sum f s
    gcastWith (sumSESplitG f s e le) $   -- f e + (sum f e - sum f s) = (f e + sum f e) - sum f s
    addAssoc (f @@ e) (monSum f e) (addInv $ monSum f s)

sumSESplitNat :: SFunction f -> SNat s -> SNat e -> s <= e -> SumSE f s e :~: Sum f e Nat.Sub.- Sum f s
sumSESplitNat f s e NatLeZ           = sym $ gcastWith (natSubNZ s) $ natSubNZ $ monSum f s
sumSESplitNat f s (SS e) (NatLeS le) =
    gcastWith (natSubSL e s le) $                       -- f (s+(e-s)) + sum (f . (s+)) (e - s) = (f e + sum f e) - sum f s
    gcastWith (natSubSplit e s le) $                    -- f e + sum (f . (s+)) (e - s) = (f e + sum f e) - sum f s
    gcastWith (sumSESplitNat f s e le) $                -- f e + (sum f e - sum f s) = (f e + sum f e) - sum f s
    natAddSubAssoc (f @@ e) (monSum f e) (monSum f s) $ -- sum f s <= sum f e
    natSumIdxLe s e f le
