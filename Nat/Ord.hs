{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE GADTs        #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Nat.Ord where

import           Add
import           Data.Kind
import           Data.Type.Equality
import           Data.Void
import           Mul
import           Nat.Add
import           Nat.Defs
import           Nat.Mul
import           Ops

data NatLe n m where
    NatLeZ :: forall n. NatLe n n
    NatLeS :: forall n m. NatLe n m -> NatLe n (S m)

instance PartOrd Nat where
    type n <= m = NatLe n m

    leRefl _ = NatLeZ
    leTrans _ _ _ aleb NatLeZ             = aleb
    leTrans a b (SS c) aleb (NatLeS blec) = NatLeS $ leTrans a b c aleb blec
    leAsym _ _ NatLeZ _           = Refl
    leAsym a (SS b) (NatLeS aleb) sblea = let sbleb = leTrans (SS b) a b sblea aleb in absurd $ natSnLeN b sbleb

natSmLeZ :: S n <= Z -> Void
natSmLeZ le = case le of {}

natLeDown :: S n <= S m -> n <= m
natLeDown NatLeZ                   = NatLeZ
natLeDown (NatLeS NatLeZ)          = NatLeS NatLeZ
natLeDown (NatLeS nlem@(NatLeS _)) = NatLeS $ natLeDown nlem

natLeDown' :: SNat n -> SNat m -> S n <= S m -> n <= m
natLeDown' n m = natLeDown

natSnLeN :: SNat n -> S n <= n -> Void
natSnLeN SZ le     = natSmLeZ le
natSnLeN (SS n) le = natSnLeN n $ natLeDown le


natZLeN :: SNat n -> Z <= n
natZLeN SZ     = NatLeZ
natZLeN (SS n) = NatLeS $ natZLeN n

natLeUp :: n <= m -> S n <= S m
natLeUp NatLeZ        = NatLeZ
natLeUp (NatLeS nlem) = NatLeS $ natLeUp nlem

natLeUp' :: SNat n -> SNat m -> n <= m -> S n <= S m
natLeUp' _ _  = natLeUp

natLeS :: S n <= m -> n <= m
natLeS NatLeZ      = NatLeS NatLeZ
natLeS (NatLeS le) = NatLeS $ natLeS le

natLeS' :: SNat n -> SNat m -> S n <= m -> n <= m
natLeS' n m = natLeS

instance TotalOrd Nat where
    leDec SZ m          = Left $ natZLeN m
    leDec n SZ          = Right $ natZLeN n
    leDec (SS n) (SS m) = case leDec n m of
        Left nlem  -> Left $ natLeUp nlem
        Right mlen -> Right $ natLeUp mlen



natLeZEqZ :: n <= Z -> n :~: Z
natLeZEqZ NatLeZ = Refl

leCastL :: (n :: Nat) :~: m -> n <= k -> m <= k
leCastL eq le = gcastWith eq le

leCastR :: (n :: Nat) :~: m -> k <= n -> k <= m
leCastR eq le = gcastWith eq le



data LeDiffEx n m where
    LeDiffEx :: SNat k -> k + n :~: m -> LeDiffEx n m
natLeDiff :: SNat n -> SNat m -> n <= m -> LeDiffEx n m
natLeDiff n m NatLeZ = LeDiffEx SZ Refl
natLeDiff n (SS m) (NatLeS le) = case natLeDiff n m le of
    LeDiffEx k eq -> LeDiffEx (SS k) $ apply Refl eq

data NatCompare :: Nat -> Nat -> Type where
    NatCmpLt :: forall n m. S n <= m -> NatCompare n m
    NatCmpEq :: forall n m. n :~: m -> NatCompare n m
    NatCmpGt :: forall n m. S m <= n -> NatCompare n m

leCompare :: SNat n -> SNat m -> NatCompare n m
leCompare n m = case leDec n m of
    Left NatLeZ       -> NatCmpEq Refl
    Left (NatLeS le)  -> let SS m' = m in NatCmpLt $ natLeUp le
    Right NatLeZ      -> NatCmpEq Refl
    Right (NatLeS le) -> let SS n' = n in NatCmpGt $ natLeUp le


natNLeNplusKL :: SNat n -> SNat k -> n <= k + n
natNLeNplusKL n SZ     = NatLeZ
natNLeNplusKL n (SS k) = NatLeS $ natNLeNplusKL n k

natNLeNplusKR :: SNat n -> SNat k -> n <= n + k
natNLeNplusKR n k = gcastWith (addComm n k) $ natNLeNplusKL n k

natNLeNKL :: SNat n -> SNat k -> n <= S k * n
natNLeNKL n k = natNLeNplusKR n $ k .*. n

natNLeNKR :: SNat n -> SNat k -> n <= n * S k
natNLeNKR n k = gcastWith (mulComm n $ SS k) $ natNLeNKL n k

natLeAddMonoL :: SNat k -> n <= m -> k + n <= k + m
natLeAddMonoL SZ eq     = eq
natLeAddMonoL (SS k) eq = natLeUp $ natLeAddMonoL k eq

natLeAddMonoR :: SNat k -> SNat n -> SNat m -> n <= m -> n + k <= m + k
natLeAddMonoR k n m le = gcastWith (addComm n k) $ gcastWith (addComm m k) $ natLeAddMonoL k le

natLeAddMonoBoth :: SNat n -> n <= m -> k <= l -> n + k <= m + l
natLeAddMonoBoth n NatLeZ le          = natLeAddMonoL n le
natLeAddMonoBoth n (NatLeS nlem) klel = NatLeS $ natLeAddMonoBoth n nlem klel


natLeAddMonoLRev :: SNat k -> SNat n -> SNat m -> k + n <= k + m -> n <= m
natLeAddMonoLRev SZ _ _ le     = le
natLeAddMonoLRev (SS k) n m le = natLeAddMonoLRev k n m $ natLeDown le

natLeAddMonoRRev :: SNat k -> SNat n -> SNat m -> n + k <= m + k -> n <= m
natLeAddMonoRRev k n m le = natLeAddMonoLRev k n m $ gcastWith (addComm n k) $ gcastWith (addComm m k) le

natLeAddSplit :: SNat n -> SNat m -> SNat k -> SNat l -> n + k <= m + l -> Either (n <= m) (k <= l)
natLeAddSplit n m k l le = case (leDec n m, leDec k l) of
    (Left nlem, _) -> Left nlem
    (_, Left klel) -> Right klel
    (Right mlen, Right llek) ->
        let sumEq = leAsym (n .+. k) (m .+. l) le $ natLeAddMonoBoth m mlen llek in
        Left $ natLeAddMonoRRev l n m $ gcastWith sumEq $ natLeAddMonoL n llek


natLeAddR :: SNat k -> SNat n -> SNat m -> n <= m -> n <= k + m
natLeAddR SZ _ _ nlem     = nlem
natLeAddR (SS k) n m nlem = NatLeS $ natLeAddR k n m nlem

natLeAddL :: SNat k -> SNat n -> SNat m -> n <= m -> n <= m + k
natLeAddL k n m nlem = gcastWith (addComm m k) $ natLeAddR k n m nlem



natLeMulMonoL :: SNat k -> SNat n -> SNat m -> n <= m -> k * n <= k * m
natLeMulMonoL SZ _ _ _        = leRefl SZ
natLeMulMonoL (SS k) n m nlem = natLeAddMonoBoth n nlem $ natLeMulMonoL k n m nlem

natLeMulMonoR :: SNat k -> SNat n -> SNat m -> n <= m -> n * k <= m * k
natLeMulMonoR k n m nlem = gcastWith (mulComm n k) $ gcastWith (mulComm m k) $ natLeMulMonoL k n m nlem

natLeMulMonoBoth :: SNat n -> SNat m -> SNat k -> SNat l -> n <= m -> k <= l -> n * k <= m * l
natLeMulMonoBoth n _ k l NatLeZ klel = natLeMulMonoL n k l klel
natLeMulMonoBoth n (SS m) k l (NatLeS nlem) klel = natLeAddR l (n .*. k) (m .*. l) $ natLeMulMonoBoth n m k l nlem klel

natLeMulMonoLRev :: SNat k -> SNat n -> SNat m -> S k * n <= S k * m -> n <= m
natLeMulMonoLRev SZ n m le = gcastWith (addZeroR n) $ gcastWith (addZeroR m) le
natLeMulMonoLRev (SS k) n m le = case natLeAddSplit n m (SS k .*. n) (SS k .*. m) le of     -- le :: n + S k * n <= m + S k * m
    Left nlem -> nlem
    Right le' -> natLeMulMonoLRev k n m le'

natLeMulMonoRRev :: SNat k -> SNat n -> SNat m -> n * S k <= m * S k -> n <= m
natLeMulMonoRRev k n m le = natLeMulMonoLRev k n m $ gcastWith (mulComm n $ SS k) $ gcastWith (mulComm m $ SS k) le

natLeMulSplit :: SNat n -> SNat m -> SNat k -> SNat l -> n * k <= m * l -> Either (n <= m) (k <= l)
natLeMulSplit n m k l le = case (leDec n m, leDec k l) of
    (Left nlem, _) -> Left nlem
    (_, Left klel) -> Right klel
    (Right mlen, Right llek) ->
        let mulEq = leAsym (n .*. k) (m .*. l) le $ natLeMulMonoBoth m n l k mlen llek in case (k, l) of
            (SZ, SZ)    -> Right NatLeZ
            (SS k', SZ) -> let Left nz = natMulIsZ n k $ trans mulEq $ natMulZ m in Left $ gcastWith nz $ natZLeN m
            (_, SS l') -> Left $ natLeMulMonoRRev l' n m $ leCastR mulEq $ natLeMulMonoL n l k llek


natMulSameL :: SNat k -> SNat n -> SNat m -> S k * n :~: S k * m -> n :~: m
natMulSameL SZ n m eq     = gcastWith (addZeroR n) $ gcastWith (addZeroR m) eq
natMulSameL (SS k) n m eq = case leCompare n m of
    NatCmpEq eq    -> eq
    NatCmpLt snlem ->
        let mul_snlem = natLeMulMonoL (SS $ SS k) (SS n) m snlem in
        let mul_snlen = leCastR (sym eq) mul_snlem in
        let unmul = natLeMulMonoLRev (SS k) (SS n) n mul_snlen in
        absurd $ natSnLeN n unmul
    NatCmpGt smlen ->
        let mul_smlen = natLeMulMonoL (SS $ SS k) (SS m) n smlen in
        let mul_smlem = leCastR eq mul_smlen in
        let unmul = natLeMulMonoLRev (SS k) (SS m) m mul_smlem in
        absurd $ natSnLeN m unmul

natMulSameR :: SNat k -> SNat n -> SNat m -> n * S k :~: m * S k -> n :~: m
natMulSameR k n m eq = gcastWith (mulComm n $ SS k) $ gcastWith (mulComm m $ SS k) $ natMulSameL k n m eq
