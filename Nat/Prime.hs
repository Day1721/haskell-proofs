{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module Nat.Prime where
import           Add
import           Data.Type.Equality
import           Data.Void
import           Nat
import           Nat.Div
import           Nat.Ord
import           Ops


type NatPrimeAll (n :: Nat) = forall m. SNat m -> N2 <= m -> NatDivides m n -> m :~: n
type NatPrime (n :: Nat) = (N2 <= n, NatPrimeAll n)

n2Prime :: NatPrime N2
n2Prime = (NatLeZ, n2PrimeAll) where
    n2PrimeAll :: NatPrimeAll N2
    n2PrimeAll m mge2 div@(NatDivides k eq) = let Right le = natDividesLe m div in case m of
        SZ        -> absurd $ natSmLeZ mge2
        SS SZ     -> absurd $ natSmLeZ $ natLeDown mge2
        SS (SS m) -> let eq' = natLeDown $ natLeDown le in gcastWith (natLeZEqZ eq') Refl

data NatComposite (n :: Nat) where
    NatComposite :: SNat k -> N2 <= k -> S k <= n -> NatDivides k n -> NatComposite n

primeCheck :: SNat n -> N2 <= n -> Either (NatPrime n) (NatComposite n)
primeCheck SZ le = case le of {}
primeCheck n@(SS n') le = case go n le n' (natLeDown le) NatLeZ of
        Left prime      -> Left (le, \m lem mdivn -> case natDividesLe m mdivn of
            Left eq  -> case eq of {}
            Right mlen -> case mlen of
                NatLeZ       -> Refl
                NatLeS mlen' -> absurd $ prime m lem mlen' mdivn
            )
        Right composite -> Right composite
    where
    le2 :: SNat n -> N2 <= N2 + n
    le2 n = natLeAddL n n2 n2 NatLeZ
    go :: SNat n -> N2 <= n -> SNat m -> N1 <= m -> S m <= n -> Either (forall k. SNat k -> N2 <= k -> k <= m -> NatDivides k n -> Void) (NatComposite n)
    go SZ le _ _                         _ = case le of {}
    go (SS SZ) le _ _                    _ = case natLeDown le of {}
    go _ _ SZ le                         _ = case le of {}
    go n@(SS (SS n')) _ (SS SZ) _        _ = Left $ \k kge2 kle1 _ -> natSnLeN n1 $ leTrans n2 k n1 kge2 kle1
    go n@(SS (SS n')) nle m@(SS m'@(SS m'')) (NatLeS mle) mlesn = case go n nle m' mle $ natLeS mlesn of
        Left prime     -> let mod = natMod n m $ NatLeS mle in case mod of
            SZ      -> Right $ NatComposite m (natLeUp $ natLeUp $ natZLeN m'') mlesn $ natModZDivides n m (NatLeS mle) Refl
            SS mod' -> Left $ \k kle klem kdivn -> case klem of
                NatLeZ       -> case natDividesModZ n k (NatLeS mle) kdivn of {}
                NatLeS klem' -> prime k kle klem' kdivn
        Right nonprime -> Right nonprime


data NatPrimeDivisor n where
    NatPrimeDivisor :: N2 <= n -> SNat p -> NatDivides p n -> NatPrime p -> NatPrimeDivisor n

natPrimeDivisor :: SNat n -> N2 <= n -> NatPrimeDivisor n
natPrimeDivisor n le = case primeCheck n le of
    Left prime     -> NatPrimeDivisor le n (natDividesRefl n) prime
    Right (NatComposite k lek klesn kdivn) -> case natPrimeDivisor k lek of
        NatPrimeDivisor _ p pdivk pprime -> NatPrimeDivisor le p (natDividesTrans p pdivk kdivn) pprime
