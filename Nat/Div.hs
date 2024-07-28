{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Nat.Div where

import           Add
import           Data.Type.Equality
import           Data.Void
import           Mul
import           Nat.Add
import           Nat.Defs
import           Nat.Mul
import           Nat.Ord
import           Nat.Sub
import           Ops
import           Prelude            hiding (divMod)
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



type family NatDivMod (n :: Nat) (m :: Nat) (div :: Nat) (mod :: Nat) :: (Nat, Nat) where
    NatDivMod Z m div mod = '(div, mod)
    NatDivMod (S n) m div Z = NatDivMod n m (S div) m
    NatDivMod (S n) m div (S mod) = NatDivMod n m div mod
divMod :: SNat n -> SNat m -> SNat div -> SNat mod -> SPair (NatDivMod n m div mod)
divMod SZ m cnt mod          = SPair cnt mod
divMod (SS n) m cnt SZ       = divMod n m (SS cnt) m
divMod (SS n) m cnt (SS mod) = divMod n m cnt mod

natNatDivModStep :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> (n + S m * d + NatSub m a :~: S m * PFst (NatDivMod n m d a) + NatSub m (PSnd (NatDivMod n m d a)), PSnd (NatDivMod n m d a) <= m)
natNatDivModStep SZ m d a alem     = (Refl, alem)
natNatDivModStep (SS n) m d SZ _ =                                      -- S n + S m * d + m = S m * div n m d a + (m - mod n m d a)
    let (eq, le) = natNatDivModStep n m (SS d) m NatLeZ
    in (
        sym $ trans (sym eq) $                   -- n + S m * S d + (m - m) = S n + S m * d + m
        gcastWith (natSubNZ m) $                 -- n + S m * S d + 0 = S n + S m * d + m
        trans (addZeroR $ n .+. SS m .*. SS d) $ -- n + S m * S d = S (n + S m * d + m)
        trans (singApplyF (f_Add @@ n) $            -- S m * S d = S (S m * d + m)
            trans (natMulS (SS m) d) $              -- S m + S m * d = S (S m * d + m)
            singApplyF f_S $ addComm m $ SS m .*. d
        ) $                                     -- n + S (S m * d + m) = S (n + S m * d + m)
        trans (natAddS n $ SS m .*. d .+. m) $  -- S (n + (S m * d + m)) = S (n + S m * d + m)
        apply Refl $                            -- n + (S m * d + m) = (n + S m * d) + m
        natAddAssoc n (SS m .*. d) m
        , le)
natNatDivModStep (SS n) m d (SS a) salem =
    let alem = natLeS salem
        (eq, le) = natNatDivModStep n m d a alem
    in (flip trans eq $                     -- S (n + S m * d + (m - S a)) = n + S m * d + (m - a)
        trans (apply Refl $
            addComm (n .+. SS m .*. d) $ natSub m (SS a) salem
        ) $                                 -- S (m - S a) + (n + S m * d) = n + S m * d + (m - a)
        gcastWith (natSubSR m a salem) $     -- (m - a) + (n + S m * d) = n + S m * d + (m - a)
        addComm (natSub m a alem) $ n .+. SS m .*. d
        , le)

natNatDivModStartLe :: SNat n -> SNat m -> PSnd (NatDivMod n m Z m) <= m
natNatDivModStartLe n m = snd $ natNatDivModStep n m SZ m NatLeZ

type family NatMod (n :: Nat) (m :: Nat) :: Nat where
    NatMod n (S m) = NatSub m (PSnd (NatDivMod n m Z m))
natMod :: SNat n -> SNat m -> N1 <= m -> SNat (NatMod n m)
natMod n SZ le    = absurd $ natSnLeN SZ le
natMod n (SS m) _ = natSub m (sPSnd $ divMod n m SZ m) $ natNatDivModStartLe n m

type family NatDiv (n :: Nat) (m :: Nat) :: Nat where
    NatDiv n (S m) = PFst (NatDivMod n m Z m)
natDiv :: SNat n -> SNat m -> N1 <= m -> SNat (NatDiv n m)
natDiv n SZ le    = absurd $ natSnLeN SZ le
natDiv n (SS m) _ = sPFst $ divMod n m SZ m


natNatDivModEq :: SNat n -> SNat m -> N1 <= m -> n :~: m * NatDiv n m  + NatMod n m
natNatDivModEq n SZ le    = absurd $ natSnLeN SZ le
natNatDivModEq n (SS m) _ = let (eq, _) = natNatDivModStep n m SZ m NatLeZ in
    flip trans eq $ sym $               -- (n + m * 0) + m - m = n
    gcastWith (natSubNZ m) $            -- (n + m * 0) + 0 = n
    trans (addZeroR $ n .+. m .*. SZ) $ -- n + m * 0 = n
    gcastWith (natMulZ m) $ addZeroR n

natDivZ :: SNat m -> N1 <= m -> NatDiv Z m :~: Z
natDivZ SZ le    = case le of {}
natDivZ (SS m) _ = Refl

natModZ :: SNat m -> N1 <= m -> NatMod Z m :~: Z
natModZ SZ le    = case le of {}
natModZ (SS m) _ = natSubNZ m

natNatDivModNN :: SNat n -> SNat m -> n <= m -> SNat d -> NatDivMod (S n) m d n :~: '(S d, m)
natNatDivModNN SZ m le _     = Refl
natNatDivModNN (SS n) m le d = natNatDivModNN n m (natLeS le) d

natModNN :: SNat n -> N1 <= n -> NatMod n n :~: Z
natModNN SZ le    = case le of {}
natModNN (SS n) _ = gcastWith (natNatDivModNN n n NatLeZ SZ) $ natSubNZ n

natNatDivModKSteps :: SNat n -> SNat m -> SNat d -> SNat a -> SNat k -> NatDivMod (k+n) m d (k+a) :~: NatDivMod n m d a
natNatDivModKSteps _ _ _ _ SZ     = Refl
natNatDivModKSteps n m d a (SS k) = natNatDivModKSteps n m d a k

natNatDivModSnN :: SNat n -> SNat d -> SNat a -> a <= n -> NatDivMod (S n) n d a :~: '(S d, a)
natNatDivModSnN n d a le =                                     -- divmod (S n) n d a = (S d, a)
    gcastWith (natSubSplit n a le) $                        -- divmod (S (a + (n - a))) n d a = (S d, a)
    gcastWith (addZeroR a) $                                -- divmod (S (a + (n - a))) n d (a + 0) = (S d, a)
    gcastWith (natAddS a $ natSub n a le) $                 -- divmod (a + S (n - a)) n d (a + 0) = (S d, a)
    trans (natNatDivModKSteps (SS $ natSub n a le) n d SZ a) $ -- divmod (n - a) n (S d) (a + (n - a)) = (S d, a)
    gcastWith (addComm a $ natSub n a le) $                 -- divmod (n - a) n (S d) ((n - a) + a) = (S d, a)
    gcastWith (addZeroR $ natSub n a le) $                  -- divmod ((n - a) + 0) n (S d) ((n - a) + a) = (S d, a)
    natNatDivModKSteps SZ n (SS d) a (natSub n a le)

natNatDivModSD :: SNat n -> SNat m -> SNat d -> SNat a -> NatDivMod n m (S d) a :~: '(S (PFst (NatDivMod n m d a)), PSnd (NatDivMod n m d a))
natNatDivModSD SZ m d a          = Refl
natNatDivModSD (SS n) m d SZ     = natNatDivModSD n m (SS d) m
natNatDivModSD (SS n) m d (SS a) = natNatDivModSD n m d a

natNatDivModAddMR :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> NatDivMod (n + S m) m d a :~: NatDivMod n m (S d) a --'(S (PFst (NatDivMod n m d a)), PSnd (NatDivMod n m d a))
natNatDivModAddMR SZ m d u le          = natNatDivModSnN m d u le
natNatDivModAddMR (SS n) m d SZ _      = natNatDivModAddMR n m (SS d) m NatLeZ
natNatDivModAddMR (SS n) m d (SS u) le = natNatDivModAddMR n m d u $ natLeS le

natNatDivModAddML :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> NatDivMod (S m + n) m d a :~: NatDivMod n m (S d) a
natNatDivModAddML n m d a le = gcastWith (addComm (SS m) n) $ natNatDivModAddMR n m d a le

natModAddM :: SNat n -> SNat m -> N1 <= m -> NatMod (n + m) m :~: NatMod n m
natModAddM n SZ le    = absurd $ natSmLeZ le
natModAddM n (SS m) _ = gcastWith (trans (natNatDivModAddMR n m SZ m NatLeZ) $ natNatDivModSD n m SZ m) Refl


natNatDivModMulM :: SNat n -> SNat m -> SNat d -> SNat a -> a <= m -> NatDivMod (n * S m) m d a :~: '(n + d, a)
natNatDivModMulM SZ _ _ _ le     = Refl
natNatDivModMulM (SS n) m d a le = trans (natNatDivModAddML (n .*. SS m) m d a le) $ gcastWith (natAddS n d) $ natNatDivModMulM n m (SS d) a le

natModMulM :: SNat n -> SNat m -> N1 <= m -> NatMod (n * m) m :~: Z
natModMulM n SZ le    = absurd $ natSmLeZ le
natModMulM n (SS m) _ = gcastWith (natNatDivModMulM n m SZ m NatLeZ) $ natSubNZ m


natModZDiv :: SNat n -> SNat m -> N1 <= m -> NatMod n m :~: Z -> m * NatDiv n m :~: n
natModZDiv n m le eq = sym $ gcastWith (addZeroR $ m .*. natDiv n m le) $ gcastWith eq $ natNatDivModEq n m le

natModZDivides :: SNat n -> SNat m -> N1 <= m -> NatMod n m :~: Z -> NatDivides m n
natModZDivides n m le eq = NatDivides (natDiv n m le) $ trans (mulComm (natDiv n m le) m) $ natModZDiv n m le eq

natDividesModZ :: SNat n -> SNat m -> N1 <= m -> NatDivides m n -> NatMod n m :~: Z
natDividesModZ n m le (NatDivides k Refl) = natModMulM k m le

natModNZDivides :: SNat n -> SNat m -> N1 <= m -> NatMod n m =/= Z -> NatDivides m n -> Void
natModNZDivides n m le neqz div = neqz $ natDividesModZ n m le div
