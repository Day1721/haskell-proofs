{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Nat.Ord where

import           Data.Type.Equality
import           Data.Void
import           Nat.Defs
import           Ops

instance PartOrd Nat where
    data n <= m where
        NatLeZ :: forall n. n <= n
        NatLeS :: forall n m. n <= m -> n <= S m

    leRefl _ = NatLeZ
    leTrans _ _ _ aleb NatLeZ             = aleb
    leTrans a b (SS c) aleb (NatLeS blec) = NatLeS $ leTrans a b c aleb blec
    leAsym _ _ NatLeZ _           = Refl
    leAsym a (SS b) (NatLeS aleb) sblea = let sbleb = leTrans (SS b) a b sblea aleb in absurd $ natSmLeM b sbleb

natSmLeZ :: SNat n -> S n <= Z -> Void
natSmLeZ SZ snLeZ = case snLeZ of {}
natSmLeZ (SS n) ssnLeZ = natSmLeZ n $ leTrans (SS n) (SS $ SS n) SZ (NatLeS NatLeZ) ssnLeZ

natLeDown :: SNat n -> SNat m -> S n <= S m -> n <= m
natLeDown _ _ NatLeZ             = NatLeZ
natLeDown n SZ (NatLeS nlem)     = absurd $ natSmLeZ n nlem
natLeDown n (SS m) (NatLeS nlem) = NatLeS $ natLeDown n m nlem

natSmLeM :: SNat m -> S m <= m -> Void
natSmLeM SZ le     = case le of {}
natSmLeM (SS n) le = natSmLeM n $ natLeDown (SS n) n le


makeZLeN :: SNat n -> Z <= n
makeZLeN SZ     = NatLeZ
makeZLeN (SS n) = NatLeS $ makeZLeN n

natLeUp :: SNat n -> SNat m -> n <= m -> S n <= S m
natLeUp _ _ NatLeZ             = NatLeZ
natLeUp n (SS m) (NatLeS nlem) = NatLeS $ natLeUp n m nlem


instance TotalOrd Nat where
  leDec SZ m          = Left $ makeZLeN m
  leDec n SZ          = Right $ makeZLeN n
  leDec (SS n) (SS m) = case leDec n m of
    Left nlem  -> Left $ natLeUp n m nlem
    Right mlen -> Right $ natLeUp m n mlen