{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fno-max-relevant-binds #-}
{-# HLINT ignore "Use camelCase" #-}

module Nat.Fact where
import           Add                hiding (type (-), (.-.))
import           Data.Type.Equality
import           Mul
import           Nat
import           Nat.Div
import           Nat.Mul
import           Nat.Ord
import           Nat.Sub
import           Ord
import           Single

type family NatFact (n :: Nat) :: Nat where
    NatFact Z = N1
    NatFact (S n) = S n * NatFact n

natFact :: SNat n -> SNat (NatFact n)
natFact SZ     = n1
natFact (SS n) = SS n .*. natFact n

type F_NatFact = F_NatFact0
data F_NatFact0 :: Nat ~> Nat
type F_NatFact1 n = NatFact n
type instance Apply F_NatFact0 n = F_NatFact1 n
f_NatFact :: SFunction F_NatFact
f_NatFact = SFunction {applyFunc = natFact}


natFactLeZ :: SNat n -> NatFact n > Z
natFactLeZ SZ     = NatLeZ
natFactLeZ (SS n) =                         -- 1 <= (S n)*n!    <==> (S n)! > 0
    natLeTrans (natLeUp $ natZLeN n) $      -- S n <= (S n)*n!
    gcastWith (mulOneR $ SS n) $            -- (S n)*1 <= (S n)*n!
    natLeMulMonoL (SS n) n1 (natFact n) $   -- 1 <= n!          <==> n! > 0
    natFactLeZ n

natFactDividesN :: SNat n -> n > Z -> NatDivides n (NatFact n)
natFactDividesN SZ le    = case le of {}
natFactDividesN (SS n) _ = NatDivides (natFact n) $ mulComm (natFact n) (SS n)


natFactDividesLeN :: SNat n -> SNat m -> m > Z -> m <= n -> NatDivides m (NatFact n)
natFactDividesLeN n m lem NatLeZ              = natFactDividesN n lem
natFactDividesLeN (SS n) m lem (NatLeS mlesn) = natDividesMulL m (SS n) $ natFactDividesLeN n m lem mlesn


natFactDividesFactLeN :: SNat n -> SNat m -> m <= n -> NatDivides (NatFact m) (NatFact n)
natFactDividesFactLeN n m NatLeZ              = natDividesRefl (natFact n)
natFactDividesFactLeN (SS n) m (NatLeS mlesn) = natDividesMulL (natFact m) (SS n) $ natFactDividesFactLeN n m mlesn


type family NatFallFact (n :: Nat) (k :: Nat) :: Nat where
    NatFallFact n Z = N1
    NatFallFact Z (S k) = Z
    NatFallFact (S n) (S k) = S n * NatFallFact n k
natFallFact :: SNat n -> SNat k -> SNat (NatFallFact n k)
natFallFact n SZ          = n1
natFallFact SZ (SS k)     = SZ
natFallFact (SS n) (SS k) = SS n .*. natFallFact n k

natFallFactSafe :: SNat n -> SNat k -> k <= n -> SNat (NatFallFact n k)
natFallFactSafe n k _ = natFallFact n k

natFallFactNN :: SNat n -> NatFallFact n n :~: NatFact n
natFallFactNN SZ     = Refl
natFallFactNN (SS n) = singApplyF (f_Mul @@ SS n) $ natFallFactNN n

natFactSplit :: SNat n -> SNat k -> k <= n -> NatFact n :~: NatFallFact n k * NatFact (n - k)
natFactSplit n SZ _           = sym $ addZeroR $ natFact n
natFactSplit SZ (SS k) le     = absurd $ natSmLeZ le
natFactSplit (SS n) (SS k) le =     -- (S n)! = (S n * ff n k) * (n - k)!
    flip trans (
        mulAssoc (SS n) (natFallFactSafe n k $ natLeDown le) $ natFact $ natSubSafe n k $ natLeDown le
    ) $                             -- S n * n! = S n * (ff n k * (n - k)!)
    singApplyF (f_Mul @@ SS n) $    -- n! = ff n k * (n - k)!
    natFactSplit n k $ natLeDown le

natFallFactTail :: SNat n -> SNat k -> S k <= n -> NatFallFact n (S k) :~: NatFallFact n k * (n - k)
natFallFactTail SZ k sklen     = case sklen of {}
natFallFactTail (SS n) k sklen = go n k (natLeDown sklen) where
    go :: SNat n -> SNat k -> k <= n -> S n * NatFallFact n k :~: NatFallFact (S n) k * (S n - k)
    go n SZ _           = apply Refl $ trans (mulOneR n) $ sym $ addZeroR n
    go SZ (SS _) le     = absurd $ natSmLeZ le
    go (SS n) (SS k) le =       -- S (S n) * (S n * ff n k) = (S (S n) * ff (S n) k) * (S n - k)
        trans (
            singApplyF (f_Mul @@ SS (SS n)) $ go n k $ natLeDown le
        ) $                     -- S (S n) * (ff (S n) k * (S n - k)) = (S (S n) * ff (S n) k) * (S n - k)
        mulAssoc (SS (SS n)) (natFallFactSafe (SS n) k $ NatLeS $ natLeDown le) $ natSubSafe (SS n) k $ NatLeS $ natLeDown le


natFallFactIdxDivides :: SNat n -> SNat k -> k > Z -> k <= n -> NatDivides k (NatFallFact n k)
natFallFactIdxDivides _ SZ lek _                         = case lek of {}
natFallFactIdxDivides n k lek NatLeZ                     = gcastWith (natFallFactNN n) $ natFactDividesN n lek
natFallFactIdxDivides (SS n) k@(SS k') lek (NatLeS klen) =
    let klesn = NatLeS klen
        nmk' = natSubSafe n k' $ natLeDown klesn
        ffnk' = natFallFactSafe n k' $ natLeDown klesn
    in                                                  -- k | S n * ff n k'
        gcastWith (natSubSplit (SS n) k klesn) $        -- k | (k + (n - k')) * ff n k'
        gcastWith (natAddMulDistR k nmk' ffnk') $       -- k | (k * ff n k' + (n - k') * ff n k')
        natDividesAdd (k .*. ffnk') (nmk' .*. ffnk') k  -- k | k * ff n k'  AND  k | (n - k') * ff n k'
            (NatDivides ffnk' $ mulComm ffnk' k) $      -- k | (n - k') * ff n k'
        gcastWith (mulComm nmk' ffnk') $                -- k | ff n k' * (n - k')
        gcastWith (natFallFactTail n k' klen) $         -- k | ff n k
        natFallFactIdxDivides n k lek klen

natFallFactIdxFactDivides :: SNat n -> SNat k -> k <= n -> NatDivides (NatFact k) (NatFallFact n k)     -- rec {struct n}
natFallFactIdxFactDivides n SZ klen                               = natDividesRefl n1
natFallFactIdxFactDivides SZ (SS k) klen                          = absurd $ natSmLeZ klen
natFallFactIdxFactDivides n k NatLeZ                              = gcastWith (natFallFactNN n) natDividesRefl $ natFact n
natFallFactIdxFactDivides n@(SS n') k@(SS k') klen@(NatLeS klen') = let
    k'len' = natLeDown klen
    nmk' = natSubSafe n' k' k'len'
    ffnk' = natFallFactSafe n' k' k'len'
    in                                                              -- k! | n * ff n' k'
        gcastWith (natSubSplit n k klen) $                          -- k! | (k + (n' - k')) * ff n' k'
        gcastWith (natAddMulDistR k nmk' ffnk') $                   -- k! | (k * ff n' k' + (n' - k') * ff n' k')
        natDividesAdd (k .*. ffnk') (nmk' .*. ffnk') (natFact k) (      -- k! | k * ff n' k'
            natDividesBoth k ffnk' k (natFact k') (natDividesRefl k) $  -- k'! | ff n' k'
            natFallFactIdxFactDivides n' k' k'len'
        ) $                                                         -- k! | (n' - k') * ff n' k'
        gcastWith (mulComm nmk' ffnk') $                            -- k! | ff n' k' * (n' - k')
        gcastWith (natFallFactTail n' k' klen') $                   -- k! | ff n' k
        natFallFactIdxFactDivides n' k klen'


natBinomDivides :: SNat n -> SNat k -> k <= n -> NatDivides (NatFact k * NatFact (n - k)) (NatFact n)
natBinomDivides n k klen =                  -- k! * (n-k)! | n!
    gcastWith (natFactSplit n k klen) $     -- k! * (n-k)! | ff n k * (n-k)!
    natDividesBoth (natFallFactSafe n k klen) (natFact $ natSubSafe n k klen) (natFact k) (natFact $ natSubSafe n k klen)
    (natFallFactIdxFactDivides n k klen) $ natDividesRefl $ natFact $ natSubSafe n k klen


type NatBinom n k = NatDiv (NatFallFact n k) (NatFact k)
type F_NatBinom = F_NatBinom0
data F_NatBinom0 :: Nat ~> Nat ~> Nat
data F_NatBinom1 (n :: Nat) :: Nat ~> Nat
type F_NatBinom2 n k = NatBinom n k
type instance Apply F_NatBinom0 n = F_NatBinom1 n
type instance Apply (F_NatBinom1 n) k = F_NatBinom2 n k

natBinom :: SNat n -> SNat k -> SNat (NatBinom n k)
natBinom n k = natDiv (natFallFact n k) (natFact k) $ natFactLeZ k

natBinomSafe :: SNat n -> SNat k -> k <= n -> SNat (NatBinom n k)
natBinomSafe n k klen = natDivSafe (natFallFactSafe n k klen) (natFact k) (natFallFactIdxFactDivides n k klen) $ natFactLeZ k
