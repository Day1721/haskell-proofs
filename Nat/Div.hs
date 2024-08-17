{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Nat.Div where

import           Add                hiding (type (-), (.-.))
import           Data.Type.Equality
import           Mul
import           Nat.Add
import           Nat.Defs
import           Nat.Mul
import           Nat.Ord
import           Nat.Sub
import           Ord
import           Single
import           STuple

data NatDivides n m where
    NatDivides :: SNat k -> k * n :~: m -> NatDivides n m


natDivides1 :: SNat n -> NatDivides N1 n
natDivides1 n = NatDivides n $ trans (mulComm n n1) $ addZeroR n

natDividesZ :: SNat n -> NatDivides n Z
natDividesZ n = NatDivides SZ Refl

natDividesLe :: SNat n -> NatDivides n m -> Either (m :~: Z) (n <= m)
natDividesLe n (NatDivides k eq) = case k of
    SZ    -> Left $ sym eq
    SS k' -> Right $ gcastWith eq $ natNLeNKL n k'


natDividesRefl :: SNat n -> NatDivides n n
natDividesRefl n = NatDivides n1 $ addZeroR n

natDividesAsym :: SNat n -> SNat m -> NatDivides n m -> NatDivides m n -> m :~: n
natDividesAsym n m (NatDivides k keq) (NatDivides l leq) = case (n, m) of
    (SZ, _)        -> trans (sym keq) $ natMulZ k
    (_, SZ)        -> flip trans leq $ sym $ natMulZ l
    (SS n', SS m') -> let
        l1 = snd $ natMulIs1 k l $              -- k * l = 1
            natMulSameR m' (k .*. l) n1 $       -- (k * l) * m = m + 0
            trans (sym $ mulAssoc k l m) $      -- k * (l * m) = m + 0
            gcastWith leq $                     -- k * n = m + 0
            trans keq $ sym $ addZeroR m
        in gcastWith l1 $ gcastWith (addZeroR m) leq

natDividesTrans :: SNat n -> NatDivides n m -> NatDivides m k -> NatDivides n k
natDividesTrans n (NatDivides i ieq) (NatDivides j jeq) =
    NatDivides (j.*.i) $            -- (j * i) * n = k
    trans (sym $ mulAssoc j i n) $  -- j * (i * n) = k
    gcastWith ieq jeq


natDividesMulL :: SNat n -> SNat k -> NatDivides n m -> NatDivides n (k*m)
natDividesMulL n k ndivm = natDividesTrans n ndivm $ NatDivides k Refl

natDividesMulR :: SNat n -> SNat m -> SNat k -> NatDivides n m -> NatDivides n (m*k)
natDividesMulR n m k ndivm = natDividesTrans n ndivm $ gcastWith (mulComm m k) $ NatDivides k Refl

natDividesBoth :: SNat n -> SNat m -> SNat k -> SNat l -> NatDivides k n -> NatDivides l m -> NatDivides (k*l) (n*m)
natDividesBoth n m k l (NatDivides i Refl) (NatDivides j Refl) = NatDivides (i.*.j) $ groupMul4SwapInner i j k l

natDividesAdd :: SNat n -> SNat m -> SNat k -> NatDivides k n -> NatDivides k m -> NatDivides k (n + m)
natDividesAdd n m k (NatDivides ln Refl) (NatDivides lm Refl) = NatDivides (ln .+. lm) $ natAddMulDistR ln lm k

-- natDividesRCast ::  m :~: k -> NatDivides n m -> NatDivides n k
-- natDividesRCast Refl div = div


type family NatDivMod (n :: Nat) (m :: Nat) (div :: Nat) (mod :: Nat) :: (Nat, Nat) where
    NatDivMod Z m div mod = '(div, mod)
    NatDivMod (S n) m div Z = NatDivMod n m (S div) m
    NatDivMod (S n) m div (S mod) = NatDivMod n m div mod
natDivMod :: SNat n -> SNat m -> SNat div -> SNat mod -> SPair (NatDivMod n m div mod)
natDivMod SZ m cnt mod          = SPair cnt mod
natDivMod (SS n) m cnt SZ       = natDivMod n m (SS cnt) m
natDivMod (SS n) m cnt (SS mod) = natDivMod n m cnt mod

natDivModStep :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> (n + S m * d + (m - a) :~: S m * PFst (NatDivMod n m d a) + (m - PSnd (NatDivMod n m d a)), PSnd (NatDivMod n m d a) <= m)
natDivModStep SZ m d a alem     = (Refl, alem)
natDivModStep (SS n) m d SZ _ =                                      -- S n + S m * d + m = S m * div n m d a + (m - mod n m d a)
    let (eq, le) = natDivModStep n m (SS d) m NatLeZ
    in (
        sym $ trans (sym eq) $                   -- n + S m * S d + (m - m) = S n + S m * d + m
        gcastWith (natSubNZ m) $                 -- n + S m * S d + 0 = S n + S m * d + m
        trans (addZeroR $ n .+. SS m .*. SS d) $ -- n + S m * S d = S (n + S m * d + m)
        trans (singApplyF (addL n) $             -- S m * S d = S (S m * d + m)
            trans (natMulS (SS m) d) $              -- S m + S m * d = S (S m * d + m)
            singApplyF f_S $ addComm m $ SS m .*. d
        ) $                                     -- n + S (S m * d + m) = S (n + S m * d + m)
        trans (natAddS n $ SS m .*. d .+. m) $  -- S (n + (S m * d + m)) = S (n + S m * d + m)
        apply Refl $                            -- n + (S m * d + m) = (n + S m * d) + m
        natAddAssoc n (SS m .*. d) m
        , le)
natDivModStep (SS n) m d (SS a) salem =
    let alem = natLeS salem
        (eq, le) = natDivModStep n m d a alem
    in (,le) $ flip trans eq $                     -- S (n + S m * d + (m - S a)) = n + S m * d + (m - a)
        trans (apply Refl $
            addComm (n .+. SS m .*. d) $ natSubSafe m (SS a) salem
        ) $                                 -- S (m - S a) + (n + S m * d) = n + S m * d + (m - a)
        gcastWith (natSubSR m a salem) $    -- (m - a) + (n + S m * d) = n + S m * d + (m - a)
        addComm (natSubSafe m a alem) $ n .+. SS m .*. d

natDivModStartLe :: SNat n -> SNat m -> PSnd (NatDivMod n m Z m) <= m
natDivModStartLe n m = snd $ natDivModStep n m SZ m NatLeZ

type family NatMod (n :: Nat) (m :: Nat) :: Nat where
    NatMod n (S m) = m - PSnd (NatDivMod n m Z m)
natMod :: SNat n -> SNat m -> m > Z -> SNat (NatMod n m)
natMod n SZ le    = absurd $ natSnLeN SZ le
natMod n (SS m) _ = natSubSafe m (sPSnd $ natDivMod n m SZ m) $ natDivModStartLe n m

natModLe :: SNat n -> SNat m -> m > Z -> S (NatMod n m) <= m
natModLe n SZ lem   = absurd $ natSmLeZ lem
natModLe n (SS m) _ = natLeUp $ natSubLe m (sPSnd $ natDivMod n m SZ m) $ natDivModStartLe n m


type family NatDiv (n :: Nat) (m :: Nat) :: Nat where
    NatDiv n (S m) = PFst (NatDivMod n m Z m)
natDiv :: SNat n -> SNat m -> m > Z -> SNat (NatDiv n m)
natDiv n SZ le    = absurd $ natSnLeN SZ le
natDiv n (SS m) _ = sPFst $ natDivMod n m SZ m


natDivSafe :: SNat n -> SNat m -> NatDivides m n -> m > Z -> SNat (NatDiv n m)
natDivSafe n m _ = natDiv n m


natDivModEq :: SNat n -> SNat m -> m > Z -> n :~: m * NatDiv n m  + NatMod n m
natDivModEq n SZ le    = absurd $ natSnLeN SZ le
natDivModEq n (SS m) _ = let (eq, _) = natDivModStep n m SZ m NatLeZ in
    flip trans eq $ sym $               -- (n + m * 0) + m - m = n
    gcastWith (natSubNZ m) $            -- (n + m * 0) + 0 = n
    trans (addZeroR $ n .+. m .*. SZ) $ -- n + m * 0 = n
    gcastWith (natMulZ m) $ addZeroR n

natDivZ :: SNat m -> m > Z -> NatDiv Z m :~: Z
natDivZ SZ le    = case le of {}
natDivZ (SS m) _ = Refl

natModZ :: SNat m -> m > Z -> NatMod Z m :~: Z
natModZ SZ le    = case le of {}
natModZ (SS m) _ = natSubNZ m

natDivModNN :: SNat n -> SNat m -> n <= m -> SNat d -> NatDivMod (S n) m d n :~: '(S d, m)
natDivModNN SZ m le _     = Refl
natDivModNN (SS n) m le d = natDivModNN n m (natLeS le) d

natModNN :: SNat n -> n > Z -> NatMod n n :~: Z
natModNN SZ le    = case le of {}
natModNN (SS n) _ = gcastWith (natDivModNN n n NatLeZ SZ) $ natSubNZ n

natDivModKSteps :: SNat n -> SNat m -> SNat d -> SNat a -> SNat k -> NatDivMod (k+n) m d (k+a) :~: NatDivMod n m d a
natDivModKSteps _ _ _ _ SZ     = Refl
natDivModKSteps n m d a (SS k) = natDivModKSteps n m d a k

natDivModSnN :: SNat n -> SNat d -> SNat a -> a <= n -> NatDivMod (S n) n d a :~: '(S d, a)
natDivModSnN n d a le =                         -- divmod (S n) n d a = (S d, a)
    let nma = natSubSafe n a le in
    gcastWith (natSubSplit n a le) $            -- divmod (S (a + (n - a))) n d a = (S d, a)
    gcastWith (addZeroR a) $                    -- divmod (S (a + (n - a))) n d (a + 0) = (S d, a)
    gcastWith (natAddS a nma) $                 -- divmod (a + S (n - a)) n d (a + 0) = (S d, a)
    trans (natDivModKSteps (SS nma) n d SZ a) $ -- divmod (n - a) n (S d) (a + (n - a)) = (S d, a)
    gcastWith (addComm a nma) $                 -- divmod (n - a) n (S d) ((n - a) + a) = (S d, a)
    gcastWith (addZeroR nma) $                  -- divmod ((n - a) + 0) n (S d) ((n - a) + a) = (S d, a)
    natDivModKSteps SZ n (SS d) a nma

natDivModSD :: SNat n -> SNat m -> SNat d -> SNat a -> NatDivMod n m (S d) a :~: '(S (PFst (NatDivMod n m d a)), PSnd (NatDivMod n m d a))
natDivModSD SZ m d a          = Refl
natDivModSD (SS n) m d SZ     = natDivModSD n m (SS d) m
natDivModSD (SS n) m d (SS a) = natDivModSD n m d a

natDivModAddMR :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> NatDivMod (n + S m) m d a :~: NatDivMod n m (S d) a
natDivModAddMR SZ m d u le          = natDivModSnN m d u le
natDivModAddMR (SS n) m d SZ _      = natDivModAddMR n m (SS d) m NatLeZ
natDivModAddMR (SS n) m d (SS u) le = natDivModAddMR n m d u $ natLeS le

natDivModAddML :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> NatDivMod (S m + n) m d a :~: NatDivMod n m (S d) a
natDivModAddML n m d a le = gcastWith (addComm (SS m) n) $ natDivModAddMR n m d a le

natModAddM :: SNat n -> SNat m -> m > Z -> NatMod (n + m) m :~: NatMod n m
natModAddM n SZ le    = absurd $ natSmLeZ le
natModAddM n (SS m) _ = gcastWith (trans (natDivModAddMR n m SZ m NatLeZ) $ natDivModSD n m SZ m) Refl


natDivModMulM :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> NatDivMod (n * S m) m d a :~: '(n + d, a)
natDivModMulM SZ _ _ _ le     = Refl
natDivModMulM (SS n) m d a le = trans (natDivModAddML (n .*. SS m) m d a le) $ gcastWith (natAddS n d) $ natDivModMulM n m (SS d) a le

natModMulM :: SNat n -> SNat m -> m > Z -> NatMod (n * m) m :~: Z
natModMulM n SZ le    = absurd $ natSmLeZ le
natModMulM n (SS m) _ = gcastWith (natDivModMulM n m SZ m NatLeZ) $ natSubNZ m


natModZDiv :: SNat n -> SNat m -> m > Z -> NatMod n m :~: Z -> m * NatDiv n m :~: n
natModZDiv n m le eq = sym $ gcastWith (addZeroR $ m .*. natDiv n m le) $ gcastWith eq $ natDivModEq n m le

natModZDivides :: SNat n -> SNat m -> m > Z -> NatMod n m :~: Z -> NatDivides m n
natModZDivides n m le eq = NatDivides (natDiv n m le) $ trans (mulComm (natDiv n m le) m) $ natModZDiv n m le eq

natDividesModZ :: SNat n -> SNat m -> m > Z -> NatDivides m n -> NatMod n m :~: Z
natDividesModZ n m le (NatDivides k Refl) = natModMulM k m le

natModNZNDivides :: SNat n -> SNat m -> m > Z -> NatMod n m =/= Z -> Not (NatDivides m n)
natModNZNDivides n m le neqz div = neqz $ natDividesModZ n m le div


natModLarge :: SNat n -> SNat m -> m > Z -> n < m -> NatMod n m :~: n
natModLarge n SZ lem snlem     = absurd $ natSmLeZ lem
natModLarge n (SS m) lem snlem =                    -- m - snd $ divmod n m 0 m = n
    gcastWith (natSubSplit m n $ natLeDown snlem) $ -- m - snd $ divmod n m 0 (n + (m - n)) = n
    gcastWith (natAddZ n) $                         -- m - snd $ divmod (n+0) m 0 (n + (m - n)) = n
    gcastWith (
        natDivModKSteps SZ m SZ (natSubSafe m n $ natLeDown snlem) n
    ) $                                             -- m - (m - n) = n
    natSubTwiceSame m n $ natLeDown snlem



natModTwiceSame :: SNat n -> SNat m -> m > Z -> NatMod (NatMod n m) m :~: NatMod n m
natModTwiceSame n m le = natModLarge (natMod n m le) m le $ natModLe n m le


type CoPrime n m = forall k. SNat k -> NatDivides k n -> NatDivides k m -> k :~: N1
