{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module IntAdd where
import           Data.Type.Equality
import           Int
import           Nat
import           Ops
import           Prelude            hiding (Int)
import           Single

type F_ZAddPos = F_ZAddPos0
data F_ZAddPos0 :: Int ~> Nat ~> Int
data F_ZAddPos1 (i :: Int) :: Nat ~> Int
type F_ZAddPos2 i n = ZAddPos i n
type family ZAddPos (i :: Int) (n :: Nat) where
    ZAddPos i Z = i
    ZAddPos i (S n) = ZAddPos (F_ZS @@ i) n
type instance Apply F_ZAddPos i = F_ZAddPos1 i
type instance Apply (F_ZAddPos1 i) n = F_ZAddPos2 i n
f_ZAddPos :: SFunction F_ZAddPos
f_ZAddPos = SFunction {applyFunc = f_ZAddPos1}
f_ZAddPos1 :: SInt i -> SFunction (F_ZAddPos1 i)
f_ZAddPos1 i = SFunction {applyFunc = zAddPos i }
zAddPos :: SInt i -> SNat n -> SInt (ZAddPos i n)
zAddPos i = \case
    SZ -> i
    SS n -> zAddPos (zS i) n

intAddPosIntSame :: SNat n -> SInt i -> SInt j -> i :~: j -> F_ZAddPos @@ i @@ n :~: F_ZAddPos @@ j @@ n
intAddPosIntSame _ _ _ Refl = Refl

type F_ZAddNeg = F_ZAddNeg0
data F_ZAddNeg0 :: Int ~> Nat ~> Int
data F_ZAddNeg1 (i :: Int) :: Nat ~> Int
type F_ZAddNeg2 i n = ZAddNeg i n
type family ZAddNeg (i :: Int) (n :: Nat) where
    ZAddNeg i Z = i
    ZAddNeg i (S n) = ZAddNeg (F_ZP @@ i) n
type instance Apply F_ZAddNeg i = F_ZAddNeg1 i
type instance Apply (F_ZAddNeg1 i) n = F_ZAddNeg2 i n
f_ZAddNeg :: SFunction F_ZAddNeg
f_ZAddNeg = SFunction {applyFunc = f_ZAddNeg1}
f_ZAddNeg1 :: SInt i -> SFunction (F_ZAddNeg1 i)
f_ZAddNeg1 i = SFunction {applyFunc = zAddNeg i }
zAddNeg :: SInt i -> SNat n -> SInt (ZAddNeg i n)
zAddNeg i = \case
    SZ -> i
    SS n -> zAddNeg (zP i) n

intAddNegIntSame :: SNat n -> SInt i -> SInt j -> i :~: j -> ZAddNeg i n :~: ZAddNeg j n
intAddNegIntSame _ _ _ Refl = Refl


instance Add Int where
    type IZ + i = i
    type IPos n + i = ZAddPos i (S n)
    type INeg n + i = ZAddNeg i (S n)

    SIZ .+. i     = i
    SIPos n .+. i = zAddPos i (SS n)
    SINeg n .+. i = zAddNeg i (SS n)


intAddPosS :: SInt i -> SNat n -> ZAddPos (ZS i) n :~: ZS (ZAddPos i n)
intAddPosS _ SZ     = Refl
intAddPosS i (SS n) = intAddPosS (zS i) n

intAddPosP :: SInt i -> SNat n -> ZAddPos (ZP i) n :~: ZP (ZAddPos i n)
intAddPosP _ SZ     = Refl
intAddPosP i (SS n) = trans (
    intAddPosIntSame n (zS $ zP i) (zP $ zS i) $ trans (intSPId i) (sym $ intPSId i)
    ) $ intAddPosP (zS i) n

intAddNegP :: SInt i -> SNat n -> ZAddNeg (ZP i) n :~: ZP (ZAddNeg i n)
intAddNegP _ SZ     = Refl
intAddNegP i (SS n) = intAddNegP (zP i) n

intAddNegS :: SInt i -> SNat n -> ZAddNeg (ZS i) n :~: ZS (ZAddNeg i n)
intAddNegS _ SZ     = Refl
intAddNegS i (SS n) = trans (
    intAddNegIntSame n (zP $ zS i) (zS $ zP i) $ trans (intPSId i) (sym $ intSPId i)
    ) $ intAddNegS (zP i) n



intAddSL :: SInt i -> SInt j -> ZS i + j :~: ZS (i + j)
intAddSL SIZ j            = Refl
intAddSL (SIPos n) j      = intAddPosS (zS j) n
intAddSL (SINeg SZ) j     = sym $ intSPId j --intAddNegS (zP j) n
intAddSL (SINeg (SS n)) j = flip trans (intAddNegS (zP $ zP j) n) $ intAddNegIntSame n (zP j) (zS $ zP $ zP j) $ sym $ intSPId $ zP j

intAddPL :: SInt i -> SInt j -> ZP i + j :~: ZP (i + j)
intAddPL SIZ j            = Refl
intAddPL (SINeg n) j      = intAddNegP (zP j) n
intAddPL (SIPos SZ) j     = sym $ intPSId j --intAddNegS (zP j) n
intAddPL (SIPos (SS n)) j = flip trans (intAddPosP (zS $ zS j) n) $ intAddPosIntSame n (zS j) (zP $ zS $ zS j) $ sym $ intPSId $ zS j


addAddPosL :: SInt i -> SNat n -> SInt j -> ZAddPos i n + j :~: ZAddPos (i + j) n
addAddPosL i SZ j     = Refl
addAddPosL i (SS n) j = trans (addAddPosL (zS i) n j) $ intAddPosIntSame n (zS i .+. j) (zS (i .+. j)) $ intAddSL i j

addAddNegL :: SInt i -> SNat n -> SInt j -> ZAddNeg i n + j :~: ZAddNeg (i + j) n
addAddNegL i SZ j     = Refl
addAddNegL i (SS n) j = trans (addAddNegL (zP i) n j) $ intAddNegIntSame n (zP i .+. j) (zP (i .+. j)) $ intAddPL i j

intAddPosZ :: SNat n -> ZAddPos IZ (S n) :~: IPos n
intAddPosZ SZ     = Refl
intAddPosZ (SS n) = flip trans (singApplyF f_ZS $ intAddPosZ n) $ intAddPosS (SIPos SZ) n

intAddNegZ :: SNat n -> ZAddNeg IZ (S n) :~: INeg n
intAddNegZ SZ     = Refl
intAddNegZ (SS n) = flip trans (singApplyF f_ZP $ intAddNegZ n) $ intAddNegP (SINeg SZ) n

instance AddMonoid Int where
    addAssoc SIZ j k       = Refl
    addAssoc (SIPos n) j k = sym $ trans (addAddPosL (zS j) n k) $ intAddPosIntSame n (zS j .+. k) (zS (j .+. k)) $ intAddSL j k
    addAssoc (SINeg n) j k = sym $ trans (addAddNegL (zP j) n k) $ intAddNegIntSame n (zP j .+. k) (zP (j .+. k)) $ intAddPL j k

    type AddZero = IZ
    addZero = SIZ
    addZeroL _ = Refl
    addZeroR SIZ       = Refl
    addZeroR (SIPos n) = intAddPosZ n
    addZeroR (SINeg n) = intAddNegZ n

intAddSR :: SInt i -> SInt j -> i + ZS j :~: ZS (i + j)
intAddSR SIZ j       = Refl
intAddSR (SIPos n) j = intAddPosS (zS j) n
intAddSR (SINeg n) j =
    trans (
        intAddNegIntSame n (zP $ zS j) (zS $ zP j) $ trans (intPSId j) $ sym $ intSPId j
    ) $ intAddNegS (zP j) n

intAddPR :: SInt i -> SInt j -> i + ZP j :~: ZP (i + j)
intAddPR SIZ j       = Refl
intAddPR (SINeg n) j = intAddNegP (zP j) n
intAddPR (SIPos n) j =
    trans (
        intAddPosIntSame n (zS $ zP j) (zP $ zS j) $ trans (intSPId j) $ sym $ intPSId j
    ) $ intAddPosP (zS j) n

intAddPosPosL :: SNat n -> SNat m -> ZAddPos (IPos n) m :~: IPos (m + n)
intAddPosPosL n SZ = Refl
intAddPosPosL n (SS m) = trans (intAddPosS (SIPos n) m) $ singApplyF f_ZS $ intAddPosPosL n m
intAddPosPosR :: SNat n -> SNat m -> ZAddPos (IPos n) m :~: IPos (n + m)
intAddPosPosR n m = trans (intAddPosPosL n m) $ apply Refl $ addComm m n
addPos3 :: SNat n -> SNat m -> IPos n + IPos m :~: IPos (S n + m)
addPos3 n m = trans (intAddPosS (SIPos m) n) $ singApplyF f_ZS $ intAddPosPosL m n


intAddNegNegL :: SNat n -> SNat m -> ZAddNeg (INeg n) m :~: INeg (m + n)
intAddNegNegL n SZ = Refl
intAddNegNegL n (SS m) = trans (intAddNegP (SINeg n) m) $ singApplyF f_ZP $ intAddNegNegL n m
intAddNegNegR :: SNat n -> SNat m -> ZAddNeg (INeg n) m :~: INeg (n + m)
intAddNegNegR n m = trans (intAddNegNegL n m) $ apply Refl $ addComm m n
addNeg3 :: SNat n -> SNat m -> INeg n + INeg m :~: INeg (S n + m)
addNeg3 n m = trans (intAddNegP (SINeg m) n) $ singApplyF f_ZP $ intAddNegNegL m n

intAddZ1 :: SInt i -> i + Z1 :~: ZS i
intAddZ1 SIZ            = Refl
intAddZ1 (SIPos n)      = intAddPosPosR (SS SZ) n
intAddZ1 (SINeg SZ)     = Refl
intAddZ1 (SINeg (SS n)) = intAddNegZ n

intAddZM1 :: SInt i -> i + ZM1 :~: ZP i
intAddZM1 SIZ            = Refl
intAddZM1 (SINeg n)      = intAddNegNegR (SS SZ) n
intAddZM1 (SIPos SZ)     = Refl
intAddZM1 (SIPos (SS n)) = intAddPosZ n

intAddRPos :: SInt i -> SNat n -> i + IPos n :~: ZAddPos i (S n)
intAddRPos i SZ     = intAddZ1 i
intAddRPos i (SS n) =               -- i + S (Ps n) = Add (S (S i)) n
    trans (intAddSR i $ SIPos n) $  -- S (i + Ps n) = Add (S (S i)) n
    flip trans (
        sym $ intAddPosS (zS i) n
    ) $                             -- S (i + Ps n) = S (Add (S i) n)
    singApplyF f_ZS $               -- i + Ps n = S (Add (S i) n)
    intAddRPos i n

intAddRNeg :: SInt i -> SNat n -> i + INeg n :~: ZAddNeg i (S n)
intAddRNeg i SZ     = intAddZM1 i
intAddRNeg i (SS n) =               -- i + S (Ps n) = Add (S (S i)) n
    trans (intAddPR i $ SINeg n) $  -- S (i + Ps n) = Add (S (S i)) n
    flip trans (
        sym $ intAddNegP (zP i) n
    ) $                             -- S (i + Ps n) = S (Add (S i) n)
    singApplyF f_ZP $               -- i + Ps n = S (Add (S i) n)
    intAddRNeg i n

instance AddComm Int where
    addComm SIZ i       = sym $ addZeroR i
    addComm (SIPos n) i = sym $ intAddRPos i n
    addComm (SINeg n) i = sym $ intAddRNeg i n

instance AddGroup Int where
    type AddInv IZ = IZ
    type AddInv (IPos n) = INeg n
    type AddInv (INeg n) = IPos n
    addInv SIZ       = SIZ
    addInv (SIPos n) = SINeg n
    addInv (SINeg n) = SIPos n
    addInvZR SIZ       = Refl
    addInvZR (SIPos n) = go n where
        go :: SNat n -> ZAddPos (INeg n) (S n) :~: IZ
        go SZ     = Refl
        go (SS n) = go n
    addInvZR (SINeg n) = go n where
        go :: SNat n -> ZAddNeg (IPos n) (S n) :~: IZ
        go SZ     = Refl
        go (SS n) = go n


intAddInvS :: SInt i -> AddInv (ZS i) :~: ZP (AddInv i)
intAddInvS SIZ            = Refl
intAddInvS (SIPos n)      = Refl
intAddInvS (SINeg SZ)     = Refl
intAddInvS (SINeg (SS n)) = Refl

intAddInvP :: SInt i -> AddInv (ZP i) :~: ZS (AddInv i)
intAddInvP SIZ            = Refl
intAddInvP (SINeg n)      = Refl
intAddInvP (SIPos SZ)     = Refl
intAddInvP (SIPos (SS n)) = Refl
