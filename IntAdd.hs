{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE UndecidableInstances #-}
module IntAdd where
import           Data.Type.Equality
import           Int
import           Nat
import           NatAdd
import           Ops
import           Prelude            hiding (Int)
import           Single

type F_ZAddPos = F_ZAddPos0
data F_ZAddPos0 :: Int ~> Nat ~> Int
data F_ZAddPos1 (i :: Int) :: Nat ~> Int
type family F_ZAddPos2 (i :: Int) (n :: Nat) where
    F_ZAddPos2 i Z = i
    F_ZAddPos2 i (S n) = F_ZAddPos2 (F_ZS @@ i) n
type instance Apply F_ZAddPos i = F_ZAddPos1 i
type instance Apply (F_ZAddPos1 i) n = F_ZAddPos2 i n
f_ZAddPos :: SFunction F_ZAddPos
f_ZAddPos = SFunction {applyFunc = f_ZAddPos1}
f_ZAddPos1 :: SInt i -> SFunction (F_ZAddPos1 i)
f_ZAddPos1 i = SFunction {applyFunc = \case
    SZ -> i
    SS n -> f_ZAddPos @@ (f_ZS @@ i) @@ n
}

intAddPosIntSame :: SNat n -> SInt i -> SInt j -> i :~: j -> F_ZAddPos @@ i @@ n :~: F_ZAddPos @@ j @@ n
intAddPosIntSame _ _ _ Refl = Refl

type F_ZAddNeg = F_ZAddNeg0
data F_ZAddNeg0 :: Int ~> Nat ~> Int
data F_ZAddNeg1 (i :: Int) :: Nat ~> Int
type family F_ZAddNeg2 (i :: Int) (n :: Nat) where
    F_ZAddNeg2 i Z = i
    F_ZAddNeg2 i (S n) = F_ZAddNeg2 (F_ZP @@ i) n
type instance Apply F_ZAddNeg i = F_ZAddNeg1 i
type instance Apply (F_ZAddNeg1 i) n = F_ZAddNeg2 i n
f_ZAddNeg :: SFunction F_ZAddNeg
f_ZAddNeg = SFunction {applyFunc = f_ZAddNeg1}
f_ZAddNeg1 :: SInt i -> SFunction (F_ZAddNeg1 i)
f_ZAddNeg1 i = SFunction {applyFunc = \case
    SZ -> i
    SS n -> f_ZAddNeg @@ (f_ZP @@ i) @@ n
}

intAddNegIntSame :: SNat n -> SInt i -> SInt j -> i :~: j -> F_ZAddNeg @@ i @@ n :~: F_ZAddNeg @@ j @@ n
intAddNegIntSame _ _ _ Refl = Refl


instance Add Int where
    type IZ + i = i
    type IPos n + i = F_ZAddPos @@ i @@ S n
    type INeg n + i = F_ZAddNeg @@ i @@ S n

    SIZ .+. i     = i
    SIPos n .+. i = f_ZAddPos @@ i @@ SS n
    SINeg n .+. i = f_ZAddNeg @@ i @@ SS n


intAddPosS :: SInt i -> SNat n -> F_ZAddPos @@ (F_ZS @@ i) @@ n :~: F_ZS @@ (F_ZAddPos @@ i @@ n)
intAddPosS _ SZ     = Refl
intAddPosS i (SS n) = intAddPosS (f_ZS @@ i) n

intAddPosP :: SInt i -> SNat n -> F_ZAddPos @@ (F_ZP @@ i) @@ n :~: F_ZP @@ (F_ZAddPos @@ i @@ n)
intAddPosP _ SZ     = Refl
intAddPosP i (SS n) = trans (
    intAddPosIntSame n (f_ZS @@ (f_ZP @@ i)) (f_ZP @@ (f_ZS @@ i)) $ trans (intSPId i) (sym $ intPSId i)
    ) $ intAddPosP (f_ZS @@ i) n

intAddNegP :: SInt i -> SNat n -> F_ZAddNeg @@ (F_ZP @@ i) @@ n :~: F_ZP @@ (F_ZAddNeg @@ i @@ n)
intAddNegP _ SZ     = Refl
intAddNegP i (SS n) = intAddNegP (f_ZP @@ i) n

intAddNegS :: SInt i -> SNat n -> F_ZAddNeg @@ (F_ZS @@ i) @@ n :~: F_ZS @@ (F_ZAddNeg @@ i @@ n)
intAddNegS _ SZ     = Refl
intAddNegS i (SS n) = trans (
    intAddNegIntSame n (f_ZP @@ (f_ZS @@ i)) (f_ZS @@ (f_ZP @@ i)) $ trans (intPSId i) (sym $ intSPId i)
    ) $ intAddNegS (f_ZP @@ i) n



intAddSL :: SInt i -> SInt j -> F_ZS @@ i + j :~: F_ZS @@ (i + j)
intAddSL SIZ j            = Refl
intAddSL (SIPos n) j      = intAddPosS (f_ZS @@ j) n
intAddSL (SINeg SZ) j     = sym $ intSPId j --intAddNegS (f_ZP @@ j) n
intAddSL (SINeg (SS n)) j = flip trans (intAddNegS (f_ZP @@ (f_ZP @@ j)) n) $ intAddNegIntSame n (f_ZP @@ j) (f_ZS @@ (f_ZP @@ (f_ZP @@ j))) $ sym $ intSPId $ f_ZP @@ j

intAddPL :: SInt i -> SInt j -> F_ZP @@ i + j :~: F_ZP @@ (i + j)
intAddPL SIZ j            = Refl
intAddPL (SINeg n) j      = intAddNegP (f_ZP @@ j) n
intAddPL (SIPos SZ) j     = sym $ intPSId j --intAddNegS (f_ZP @@ j) n
intAddPL (SIPos (SS n)) j = flip trans (intAddPosP (f_ZS @@ (f_ZS @@ j)) n) $ intAddPosIntSame n (f_ZS @@ j) (f_ZP @@ (f_ZS @@ (f_ZS @@ j))) $ sym $ intPSId $ f_ZS @@ j


addAddPosL :: SInt i -> SNat n -> SInt j -> F_ZAddPos @@ i @@ n + j :~: F_ZAddPos @@ (i + j) @@ n
addAddPosL i SZ j     = Refl
addAddPosL i (SS n) j = trans (addAddPosL (f_ZS @@ i) n j) $ intAddPosIntSame n (f_ZS @@ i .+. j) (f_ZS @@ (i .+. j)) $ intAddSL i j

addAddNegL :: SInt i -> SNat n -> SInt j -> F_ZAddNeg @@ i @@ n + j :~: F_ZAddNeg @@ (i + j) @@ n
addAddNegL i SZ j     = Refl
addAddNegL i (SS n) j = trans (addAddNegL (f_ZP @@ i) n j) $ intAddNegIntSame n (f_ZP @@ i .+. j) (f_ZP @@ (i .+. j)) $ intAddPL i j

intAddPosZ :: SNat n -> F_ZAddPos @@ IZ @@ S n :~: IPos n
intAddPosZ SZ     = Refl
intAddPosZ (SS n) = flip trans (singApplyF f_ZS $ intAddPosZ n) $ intAddPosS (SIPos SZ) n

intAddNegZ :: SNat n -> F_ZAddNeg @@ IZ @@ S n :~: INeg n
intAddNegZ SZ     = Refl
intAddNegZ (SS n) = flip trans (singApplyF f_ZP $ intAddNegZ n) $ intAddNegP (SINeg SZ) n

instance AddMonoid Int where
    addAssoc SIZ j k       = Refl
    addAssoc (SIPos n) j k = sym $ trans (addAddPosL (f_ZS @@ j) n k) $ intAddPosIntSame n (f_ZS @@ j .+. k) (f_ZS @@ (j .+. k)) $ intAddSL j k
    addAssoc (SINeg n) j k = sym $ trans (addAddNegL (f_ZP @@ j) n k) $ intAddNegIntSame n (f_ZP @@ j .+. k) (f_ZP @@ (j .+. k)) $ intAddPL j k

    type AddZero = IZ
    addZero = SIZ
    addZeroL _ = Refl
    addZeroR SIZ       = Refl
    addZeroR (SIPos n) = intAddPosZ n
    addZeroR (SINeg n) = intAddNegZ n

intAddSR :: SInt i -> SInt j -> i + F_ZS @@ j :~: F_ZS @@ (i + j)
intAddSR SIZ j       = Refl
intAddSR (SIPos n) j = intAddPosS (f_ZS @@ j) n
intAddSR (SINeg n) j =
    trans (
        intAddNegIntSame n (f_ZP @@ (f_ZS @@ j)) (f_ZS @@ (f_ZP @@ j)) $ trans (intPSId j) $ sym $ intSPId j
    ) $ intAddNegS (f_ZP @@ j) n

intAddPR :: SInt i -> SInt j -> i + F_ZP @@ j :~: F_ZP @@ (i + j)
intAddPR SIZ j       = Refl
intAddPR (SINeg n) j = intAddNegP (f_ZP @@ j) n
intAddPR (SIPos n) j =
    trans (
        intAddPosIntSame n (f_ZS @@ (f_ZP @@ j)) (f_ZP @@ (f_ZS @@ j)) $ trans (intSPId j) $ sym $ intPSId j
    ) $ intAddPosP (f_ZS @@ j) n

intAddPosPosL :: SNat n -> SNat m -> F_ZAddPos @@ IPos n @@ m :~: IPos (m + n)
intAddPosPosL n SZ = Refl
intAddPosPosL n (SS m) = trans (intAddPosS (SIPos n) m) $ singApplyF f_ZS $ intAddPosPosL n m
intAddPosPosR :: SNat n -> SNat m -> F_ZAddPos @@ IPos n @@ m :~: IPos (n + m)
intAddPosPosR n m = trans (intAddPosPosL n m) $ apply Refl $ addComm m n


intAddNegNegL :: SNat n -> SNat m -> F_ZAddNeg @@ INeg n @@ m :~: INeg (m + n)
intAddNegNegL n SZ = Refl
intAddNegNegL n (SS m) = trans (intAddNegP (SINeg n) m) $ singApplyF f_ZP $ intAddNegNegL n m
intAddNegNegR :: SNat n -> SNat m -> F_ZAddNeg @@ INeg n @@ m :~: INeg (n + m)
intAddNegNegR n m = trans (intAddNegNegL n m) $ apply Refl $ addComm m n

intAddZ1 :: SInt i -> i + Z1 :~: F_ZS @@ i
intAddZ1 SIZ            = Refl
intAddZ1 (SIPos n)      = intAddPosPosR (SS SZ) n
intAddZ1 (SINeg SZ)     = Refl
intAddZ1 (SINeg (SS n)) = intAddNegZ n

intAddZM1 :: SInt i -> i + ZM1 :~: F_ZP @@ i
intAddZM1 SIZ            = Refl
intAddZM1 (SINeg n)      = intAddNegNegR (SS SZ) n
intAddZM1 (SIPos SZ)     = Refl
intAddZM1 (SIPos (SS n)) = intAddPosZ n

intAddRPos :: SInt i -> SNat n -> i + IPos n :~: F_ZAddPos @@ i @@ S n
intAddRPos i SZ     = intAddZ1 i
intAddRPos i (SS n) =               -- i + S (Ps n) = Add (S (S i)) n
    trans (intAddSR i $ SIPos n) $  -- S (i + Ps n) = Add (S (S i)) n
    flip trans (
        sym $ intAddPosS (f_ZS @@ i) n
    ) $                             -- S (i + Ps n) = S (Add (S i) n)
    singApplyF f_ZS $               -- i + Ps n = S (Add (S i) n)
    intAddRPos i n

intAddRNeg :: SInt i -> SNat n -> i + INeg n :~: F_ZAddNeg @@ i @@ S n
intAddRNeg i SZ     = intAddZM1 i
intAddRNeg i (SS n) =               -- i + S (Ps n) = Add (S (S i)) n
    trans (intAddPR i $ SINeg n) $  -- S (i + Ps n) = Add (S (S i)) n
    flip trans (
        sym $ intAddNegP (f_ZP @@ i) n
    ) $                             -- S (i + Ps n) = S (Add (S i) n)
    singApplyF f_ZP $               -- i + Ps n = S (Add (S i) n)
    intAddRNeg i n

instance AddComm Int where
    addComm SIZ i       = sym $ addZeroR i
    addComm (SIPos n) i = sym $ intAddRPos i n
    addComm (SINeg n) i = sym $ intAddRNeg i n
