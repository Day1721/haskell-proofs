{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Int.Mul where

import           Add
import           Data.Type.Equality
import           Distribution.Compat.Lens (_1)
import           Int.Add
import           Int.Defs
import           Mul
import           Nat
import           Prelude                  hiding (Int)
import           Single

type F_IntMulNat = F_IntMulNat0
data F_IntMulNat0 :: Int ~> Nat ~> Int
data F_IntMulNat1 (i :: Int) :: Nat ~> Int
type F_IntMulNat2 i n = IntMulNat i n
type family IntMulNat (i :: Int) (n :: Nat) :: Int where
    IntMulNat i Z = IZ
    IntMulNat i (S n) = i + IntMulNat i n
type instance Apply F_IntMulNat0 i = F_IntMulNat1 i
type instance Apply (F_IntMulNat1 i) n = F_IntMulNat2 i n
f_IntMulNat :: SFunction F_IntMulNat
f_IntMulNat = SFunction {applyFunc = f_IntMulNat1}
f_IntMulNat1 :: Sing i -> SFunction (F_IntMulNat1 i)
f_IntMulNat1 i = SFunction {applyFunc = intMulNat i}
intMulNat :: SInt i -> SNat n -> SInt (IntMulNat i n)
intMulNat i SZ     = SIZ
intMulNat i (SS n) = i .+. intMulNat i n

instance Mul Int where
    type IZ * i = IZ
    type IPos n * i = IntMulNat i (S n)
    type INeg n * i = IntMulNat (AddInv i) (S n)
    SIZ .*. i     = SIZ
    SIPos n .*. i = intMulNat i $ SS n
    SINeg n .*. i = intMulNat (addInv i) $ SS n

intMulNatZ :: SNat n -> IntMulNat IZ n :~: IZ
intMulNatZ SZ     = Refl
intMulNatZ (SS n) = intMulNatZ n

intMulZ :: SInt i -> i * IZ :~: IZ
intMulZ SIZ       = Refl
intMulZ (SIPos n) = intMulNatZ n
intMulZ (SINeg n) = intMulNatZ n

intMulNatInv :: SInt i -> SNat n -> IntMulNat (AddInv i) n :~: AddInv (IntMulNat i n)
intMulNatInv i SZ     = Refl
intMulNatInv i (SS n) =  flip trans (sym $ groupInvAddSwap i $ intMulNat i n) $
    flip trans (addComm (addInv i) $ addInv $ intMulNat i n) $
    singApplyF (f_Add @@ addInv i) $
    intMulNatInv i n

intMulInvL :: SInt i -> SInt j -> AddInv (i * j) :~: AddInv i * j
intMulInvL SIZ j       = Refl
intMulInvL (SIPos n) j = sym $ intMulNatInv j (SS n)
intMulInvL (SINeg n) j = gcastWith (groupInvTwiceSame j) $ sym $ intMulNatInv (addInv j) (SS n)

intMulInvR :: SInt i -> SInt j -> AddInv (i * j) :~: i * AddInv j
intMulInvR SIZ j       = Refl
intMulInvR (SIPos n) j = sym $ intMulNatInv j (SS n)
intMulInvR (SINeg n) j = gcastWith (groupInvTwiceSame j) $ sym $ intMulNatInv (addInv j) (SS n)


intAddMulNatDist :: SInt i -> SInt j -> SNat n -> IntMulNat (i + j) n :~: IntMulNat i n + IntMulNat j n
intAddMulNatDist i j SZ = Refl
intAddMulNatDist i j (SS n) =                                               -- (i + j) + mul (i + j) n = (i + mul i n) + (j + mul j n)
    flip trans (groupAdd4SwapInner i j (intMulNat i n) $ intMulNat j n) $   -- (i + j) + mul (i + j) n = (i + j) + (mul i n + mul j n)
    singApplyF (f_Add @@ (i .+. j)) $ intAddMulNatDist i j n

intAddMulDistL :: SInt i -> SInt j -> SInt k -> k * (i + j) :~: k * i + k * j
intAddMulDistL i j SIZ       = Refl
intAddMulDistL i j (SIPos n) = intAddMulNatDist i j $ SS n
intAddMulDistL i j (SINeg n) = gcastWith (trans (groupInvAddSwap i j) $ addComm (addInv j) (addInv i)) $ intAddMulNatDist (addInv i) (addInv j) $ SS n

intMulSL :: SInt i -> SInt j -> ZS i * j :~: j + i * j
intMulSL SIZ j        = Refl
intMulSL (SIPos n) j  = Refl
intMulSL (SINeg SZ) j = sym $           -- j + (inv j + 0) = 0
    let k = SIZ in
    trans (addAssoc j (addInv j) k) $   -- (j + inv j) + 0 = 0
    gcastWith (addInvZR j) Refl
intMulSL (SINeg (SS n)) j = sym $
    let k = intMulNat (addInv j) $ SS n in
    trans (addAssoc j (addInv j) k) $
    gcastWith (addInvZR j) Refl

intMulPL :: SInt i -> SInt j -> ZP i * j :~: AddInv j + i * j
intMulPL SIZ j        = Refl
intMulPL (SINeg n) j  = Refl
intMulPL (SIPos SZ) j = sym $
    let k = SIZ in
    trans (addAssoc (addInv j) j k) $
    gcastWith (addInvZL j) Refl
intMulPL (SIPos (SS n)) j = sym $
    let k = intMulNat j $ SS n in
    trans (addAssoc (addInv j) j k) $
    gcastWith (addInvZL j) Refl


intMulNatS :: SInt i -> SNat n -> IntMulNat (ZS i) n :~: N2I n + IntMulNat i n
intMulNatS i SZ     = Refl
intMulNatS i (SS n) = go i n where
    go :: SInt i -> SNat n -> IntMulNat (ZS i) (S n) :~: IPos n + IntMulNat i (S n)
    go i SZ = intAddSL i SIZ
    go i (SS n) =                                                           -- S i + mul (S i) (S n) = S (pos n) + (i + mul i (S n))
        trans (intAddSL i $ intMulNat (zS i) $ SS n) $                      -- S (i + mul (S i) (S n)) = S (pos n) + (i + mul i (S n))
        flip trans (sym $ intAddSL (SIPos n) $ i .+. intMulNat i (SS n)) $  -- S (i + mul (S i) (S n)) = S (pos n + (i + mul i (S n)))
        singApplyF f_ZS $                                                   -- i + mul (S i) (S n) = pos n + (i + mul i (S n))
        flip trans (addFlipL i (SIPos n) $ intMulNat i (SS n)) $            -- i + mul (S i) (S n) = i + (pos n + mul i (S n))
        singApplyF (f_Add @@ i) $ go i n

intMulNatP :: SInt i -> SNat n -> IntMulNat (ZP i) n :~: AddInv (N2I n) + IntMulNat i n
intMulNatP i SZ     = Refl
intMulNatP i (SS n) = go i n where
    go :: SInt i -> SNat n -> IntMulNat (ZP i) (S n) :~: INeg n + IntMulNat i (S n)
    go i SZ = intAddPL i SIZ
    go i (SS n) =
        trans (intAddPL i $ intMulNat (zP i) $ SS n) $
        flip trans (sym $ intAddPL (SINeg n) $ i .+. intMulNat i (SS n)) $
        singApplyF f_ZP $
        flip trans (addFlipL i (SINeg n) $ intMulNat i (SS n)) $
        singApplyF (f_Add @@ i) $ go i n

intMulSR :: SInt i -> SInt j -> i * ZS j :~: i + i * j
intMulSR SIZ j       = Refl
intMulSR (SIPos n) j = intMulNatS j $ SS n
intMulSR (SINeg n) j = gcastWith (intAddInvS j) $ intMulNatP (addInv j) (SS n)

intMulPR :: SInt i -> SInt j -> i * ZP j :~: AddInv i + i * j
intMulPR SIZ j       = Refl
intMulPR (SIPos n) j = gcastWith (intAddInvP j) $ intMulNatP j (SS n)
intMulPR (SINeg n) j = gcastWith (intAddInvP j) $ intMulNatS (addInv j) (SS n)


intMulPos3 :: SNat n -> SNat m -> IPos n * IPos m :~: N2I (S n * S m)
intMulPos3 SZ m     = gcastWith (addZeroR m) $ addZeroR $ SIPos m
intMulPos3 (SS n) m =                                       -- pos m + pos n * pos m = n2i$ S m + S n * S m
    flip trans (sym $ intAddN2I (SS m) (SS n .*. SS m)) $   -- pos m + pos n * pos m = pos m + n2i$ S n * S m
    singApplyF (f_Add @@ SIPos m) $ intMulPos3 n m
intMulNeg3 :: SNat n -> SNat m -> INeg n * INeg m :~: N2I (S n * S m)
intMulNeg3 = intMulPos3

intMulNegPos :: SNat n -> SNat m -> INeg n * IPos m :~: AddInv (N2I (S n * S m))
intMulNegPos n m = gcastWith (intMulPos3 n m) $ sym $ intMulInvL (SIPos n) $ SIPos m
intMulPosNeg :: SNat n -> SNat m -> IPos n * INeg m :~: AddInv (N2I (S n * S m))
intMulPosNeg = intMulNegPos


intAddMulDistR :: SInt i -> SInt j -> SInt k -> (i + j) * k :~: i * k + j * k
intAddMulDistR SIZ j k        = Refl
intAddMulDistR (SIPos SZ) j k = gcastWith (addZeroR k) $ intMulSL j k
intAddMulDistR (SIPos (SS n)) j k =                     -- (pos n + S j) * k :~: (k + pos n * k) + j * k
    gcastWith (intAddSR (SIPos n) j) $                  -- S (pos n + j) * k :~: (k + pos n * k) + j * k
    trans (intMulSL (SIPos n .+. j) k) $                -- k + (pos n + j) * k :~: (k + pos n * k) + j * k
    flip trans (addAssoc k (SIPos n .*. k) (j .*. k)) $ -- k + (pos n + j) * k :~: k + (pos n * k + j * k)
    singApplyF (f_Add @@ k) $                           -- (pos n + j) * k :~: pos n * k + j * k
    intAddMulDistR (SIPos n) j k
intAddMulDistR (SINeg SZ) j k = gcastWith (addZeroR $ addInv k) $ intMulPL j k
intAddMulDistR (SINeg (SS n)) j k =                                 -- (neg n + P j) * k :~: (inv k + neg n * k) + j * k
    gcastWith (intAddPR (SINeg n) j) $                              -- P (neg n + j) * k :~: (inv k + neg n * k) + j * k
    trans (intMulPL (SINeg n .+. j) k) $                            -- inv k + (neg n + j) * k :~: (inv k + neg n * k) + j * k
    flip trans (addAssoc (addInv k) (SINeg n .*. k) (j .*. k)) $    -- inv k + (neg n + j) * k :~: inv k + (pos n * k + j * k)
    singApplyF (f_Add @@ addInv k) $                                -- (neg n + j) * k :~: neg n * k + j * k
    intAddMulDistR (SINeg n) j k



instance MulMonoid Int where
    mulAssoc SIZ j k = Refl
    mulAssoc (SIPos n) j k = go n j k where
        go :: SNat n -> SInt j -> SInt k -> IPos n * (j * k) :~: (IPos n * j) * k
        go SZ j k     = gcastWith (addZeroR j) $ addZeroR $ j .*. k
        go (SS n) j k =                                                 -- j * k + pos n * (j * k) = (j + pos n * j) * k
            flip trans (sym $ intAddMulDistR j (SIPos n .*. j) k) $     -- j * k + pos n * (j * k) = j * k + (pos n * j) * k
            singApplyF (f_Add @@ (j .*. k)) $ go n j k
    mulAssoc (SINeg n) j k = go n j k where
        go :: SNat n -> SInt j -> SInt k -> INeg n * (j * k) :~: (INeg n * j) * k
        go SZ j k = gcastWith (addZeroR $ addInv j) $ trans (addZeroR $ addInv $ j .*. k) $ intMulInvL j k
        go (SS n) j k =                                                         -- inv (j * k) + neg n * (j * k) = (inv j + neg n * j) * k
            flip trans (sym $ intAddMulDistR (addInv j) (SINeg n .*. j) k) $    -- inv (j * k) + neg n * (j * k) = inv j * k + (neg n * j) * k
            gcastWith (intMulInvL j k) $                                        -- inv j * k + neg n * (j * k) = inv j * k + (neg n * j) * k
            singApplyF (f_Add @@ (addInv j .*. k)) $ go n j k
    type MulOne = Z1
    mulOneL = addZeroR
    mulOneR SIZ            = Refl
    mulOneR (SIPos SZ)     = Refl
    mulOneR (SIPos (SS n)) = singApplyF f_ZS $ mulOneR (SIPos n)
    mulOneR (SINeg SZ)     = Refl
    mulOneR (SINeg (SS n)) = singApplyF f_ZP $ mulOneR (SINeg n)


instance AddMulRing Int where
  addMulDistL = intAddMulDistL
  addMulDistR = intAddMulDistR


mulM1R :: SInt i -> i * ZM1 :~: AddInv i
mulM1R SIZ            = Refl
mulM1R (SIPos SZ)     = Refl
mulM1R (SIPos (SS n)) = singApplyF f_ZP $ mulM1R $ SIPos n
mulM1R (SINeg SZ)     = Refl
mulM1R (SINeg (SS n)) = singApplyF f_ZS $ mulM1R $ SINeg n

instance MulComm Int where
    mulComm SIZ b = sym $ intMulZ b
    mulComm (SIPos n) b = go n b where
        go :: SNat n -> SInt b -> IPos n * b :~: b * IPos n
        go SZ b = trans (addZeroR b) $ sym $ mulOneR b
        go (SS n) b = trans (singApplyF (f_Add @@ b) $ go n b) $
            sym $ intMulSR b $ SIPos n
    mulComm (SINeg n) b = go n b where
        go :: SNat n -> SInt b -> INeg n * b :~: b * INeg n
        go SZ b = trans (addZeroR $ addInv b) $ sym $ mulM1R b
        go (SS n) b = trans (singApplyF (f_Add @@ addInv b) $ go n b) $
            sym $ intMulPR b $ SINeg n
