{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Nat.Sub where

import           Add                hiding (type (-), (.-.))
import           Data.Type.Equality
import           Nat.Add
import           Nat.Defs
import           Nat.Ord
import           Ord
import           Single

type family (-) (n :: Nat) (m :: Nat) :: Nat where
    n - Z = n
    Z - m = Z
    (S n) - (S m) = n - m
type NatSub n m = n - m

(.-.) :: SNat n -> SNat m -> SNat (n - m)
n .-. SZ          = n
SZ .-. m          = SZ
(SS n) .-. (SS m) = n .-. m
natSub = (.-.)


natSubSafe :: SNat n -> SNat m -> m <= n -> SNat (n - m)
natSubSafe n m _ = n .-. m

natSubNZ :: SNat n -> n - n :~: Z
natSubNZ SZ     = Refl
natSubNZ (SS n) = natSubNZ n

natSubSL :: SNat n -> SNat m -> m <= n -> S n - m :~: S (n - m)
natSubSL _ SZ _           = Refl
natSubSL SZ (SS m) le     = absurd $ natSmLeZ le
natSubSL (SS n) (SS m) le = natSubSL n m $ natLeDown le

natSubSR :: SNat n -> SNat m -> m < n -> S (n - S m) :~: n - m
natSubSR n m = sym . natSubSL n (SS m)

natSubSplit :: SNat n -> SNat m -> m <= n -> n :~: m + (n - m)
natSubSplit n SZ le          = Refl
natSubSplit SZ (SS m) le     = absurd $ natSmLeZ le
natSubSplit (SS n) (SS m) le = apply Refl $ natSubSplit n m $ natLeDown le


natSubApplyL :: SNat k -> n :~: m -> n - k :~: m - k
natSubApplyL _ Refl = Refl

natSubApplyR :: SNat k -> n :~: m -> k - n :~: k - n
natSubApplyR _ Refl = Refl

natSubLe :: SNat n -> SNat m -> m <= n -> n - m <= n
natSubLe n SZ le          = NatLeZ
natSubLe SZ (SS m) le     = absurd $ natSmLeZ le
natSubLe (SS n) (SS m) le = natLeTrans (natSubLe n m $ natLeDown le) $ NatLeS NatLeZ

natSubTwiceSame :: SNat n -> SNat m -> m <= n -> n - (n - m) :~: m
natSubTwiceSame n SZ _           = natSubNZ n
natSubTwiceSame SZ (SS n) le     = absurd $ natSmLeZ le
natSubTwiceSame (SS n) (SS m) le =
    trans (
        natSubSL n (natSubSafe n m $ natLeDown le) $
        natSubLe n m $ natLeDown le
    ) $ apply Refl $ natSubTwiceSame n m $ natLeDown le

natAddSubSame :: SNat n -> SNat m -> (n + m) - m :~: n
natAddSubSame n SZ     = addZeroR n
natAddSubSame n (SS m) = gcastWith (natAddS n m) $ natAddSubSame n m

natAddSubAssoc :: SNat n -> SNat m -> SNat k -> k <= m -> n + (m - k) :~: (n + m) - k
natAddSubAssoc n _ k NatLeZ = gcastWith (natSubNZ k) $ gcastWith (natAddSubSame n k) $ addZeroR n
natAddSubAssoc n (SS m) k (NatLeS le) = -- n + (S m - k) = (n + S m) - k
    gcastWith (natSubSL m k le) $       -- n + S (m - k) = (n + S m) - k
    trans (natAddS n $ m .-. k) $       -- S n + (m - k) = (n + S m) - k
    gcastWith (natAddS n m) $           -- S n + (m - k) = S (n + m) - k
    gcastWith (natSubSL (n .+. m) k $       -- k <= n + m
        natLeTrans le $ natNLeNplusKL m n
    ) $                                 -- S n + (m - k) = S ((n + m) - k)
    apply Refl $ natAddSubAssoc n m k le
