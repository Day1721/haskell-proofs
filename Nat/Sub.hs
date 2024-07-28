{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module Nat.Sub where

import           Add
import           Data.Type.Equality
import           Data.Void
import           Nat
import           Nat.Ord
import           Ops
import           Single

type family NatSub (n :: Nat) (m :: Nat) :: Nat where
    NatSub n Z = n
    NatSub (S n) (S m) = NatSub n m

natSub :: SNat n -> SNat m -> m <= n -> SNat (NatSub n m)
natSub n SZ _           = n
natSub SZ (SS m) le     = absurd $ natSmLeZ le
natSub (SS n) (SS m) le = natSub n m $ natLeDown le

natSubNZ :: SNat n -> NatSub n n :~: Z
natSubNZ SZ     = Refl
natSubNZ (SS n) = natSubNZ n

natSubSL :: SNat n -> SNat m -> m <= n -> NatSub (S n) m :~: S (NatSub n m)
natSubSL _ SZ _           = Refl
natSubSL SZ (SS m) le     = absurd $ natSmLeZ le
natSubSL (SS n) (SS m) le = natSubSL n m $ natLeDown le

natSubSR :: SNat n -> SNat m -> S m <= n -> S (NatSub n (S m)) :~: NatSub n m
natSubSR n m = sym . natSubSL n (SS m)

natSubSplit :: SNat n -> SNat m -> m <= n -> n :~: m + NatSub n m
natSubSplit n SZ le          = Refl
natSubSplit SZ (SS m) le     = absurd $ natSmLeZ le
natSubSplit (SS n) (SS m) le = apply Refl $ natSubSplit n m $ natLeDown le


natSubApplyL :: SNat k -> n :~: m -> NatSub n k :~: NatSub m k
natSubApplyL _ Refl = Refl

natSubApplyR :: SNat k -> n :~: m -> NatSub k n :~: NatSub k n
natSubApplyR _ Refl = Refl
