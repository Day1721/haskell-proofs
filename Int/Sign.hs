{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module Int.Sign where

import           Add
import           Data.Type.Equality
import           Int.Add
import           Int.Defs
import           Int.Mul
import           Int.Ord
import           Nat
import           Ops
import           Prelude            hiding (Int, abs)
import           Single


instance Absolute Int where
    type Abs IZ = IZ
    type Abs (IPos n) = IPos n
    type Abs (INeg n) = IPos n
    abs SIZ       = SIZ
    abs (SIPos n) = SIPos n
    abs (SINeg n) = SIPos n
    absGeZ SIZ       = IntNatEx SZ
    absGeZ (SIPos n) = gcastWith (addComm SIZ $ SIPos n) $ IntNatEx $ SS n
    absGeZ (SINeg n) = gcastWith (addComm SIZ $ SIPos n) $ IntNatEx $ SS n
    absZIffZ SIZ _        = Refl
    absZIffZ (SIPos _) eq = case eq of {}
    absZIffZ (SINeg _) eq = case eq of {}
    absMul SIZ _               = Refl
    absMul a SIZ               = gcastWith (intMulZ a) $ sym $ intMulZ $ abs a
    absMul (SIPos n) (SIPos m) = gcastWith (intMulPos3 n m) Refl
    absMul (SINeg n) (SINeg m) = gcastWith (intMulNeg3 n m) Refl
    absMul (SIPos n) (SINeg m) = gcastWith (intMulPosNeg n m) $ gcastWith (intMulPos3 n m) Refl
    absMul (SINeg n) (SIPos m) = gcastWith (intMulNegPos n m) $ gcastWith (intMulNeg3 n m) Refl
    absTriangle SIZ b = gcastWith (addInvZR $ abs b) IntNatEx SZ
    absTriangle a SIZ = gcastWith (addZeroR a) $ gcastWith (addZeroR $ abs a) $ gcastWith (addInvZR $ abs a) IntNatEx SZ
    absTriangle (SIPos n) (SIPos m) = gcastWith (addPos3 n m) $ gcastWith (addInvZR $ SIPos $ n .+. m) IntNatEx SZ
    absTriangle (SINeg n) (SINeg m) = gcastWith (addNeg3 n m) $ gcastWith (addPos3 n m) $ gcastWith (addInvZR $ SIPos $ n .+. m) IntNatEx SZ
    absTriangle (SIPos n) (SINeg m) = case SIPos n .+. SINeg m of       -- exists k, pos k = pos n + pos m - abs (pos n + neg m)
        SIZ     -> flip castWith (IntNatEx $ SS (SS n) .+. m) $ apply Refl $
            trans (sym $ addPos3 n m) $ sym $ addZeroR $ SIPos n .+. SIPos m
        SIPos k -> flip castWith (IntNatEx $ SS (SS m) .+. m) $ apply Refl $        -- pos (S m + m) = (pos n + pos m) + inv (pos k)   where  pos k = pos n + neg m
            trans (sym $ addPos3 m m) $                                             -- pos m + pos m = (pos n + pos m) + inv (pos k)   where  pos k = pos n + neg m   ====  (pos n + pos m) + (pos m + neg n)
            sym $ trans (singApplyF (f_Add @@ (SIPos n .+. SIPos m)) $
                trans (groupInvSubSwap (SIPos n) (SIPos m)) (addComm (SIPos m) (SINeg n))
            ) $                                                                     -- (pos n + pos m) + (neg n + pos m) = pos m + pos m
            trans (groupAdd4SwapInner (SIPos n) (SIPos m) (SINeg n) (SIPos m)) $    -- (pos n + neg n) + (pos m + pos m) = pos m + pos m
            singApplyF (f_Flip @@ f_Add @@ (SIPos m .+. SIPos m)) $ addInvZR $ SIPos n
        SINeg k -> flip castWith (IntNatEx $ SS (SS n) .+. n) $ apply Refl $        -- pos (S n + n) = (pos n + pos m) + (pos n + neg m)
            trans (sym $ addPos3 n n) $ sym $                                       -- (pos n + pos m) + (pos n + neg m) = pos n + pos n
            trans (groupAdd4SwapInner (SIPos n) (SIPos m) (SIPos n) (SINeg m)) $    -- (pos n + pos n) + (pos m + neg m) = pos n + pos n
            flip trans (addZeroR $ SIPos n .+. SIPos n) $                           -- (pos n + pos n) + (pos m + neg m) = (pos n + pos n) + 0
            singApplyF (f_Add @@ (SIPos n .+. SIPos n)) $                           -- pos m + neg m = 0
            addInvZR (SIPos m)
    absTriangle (SINeg n) (SIPos m) =               -- abs (neg n + pos m) = pos n + pos m
        gcastWith (addComm (SINeg n) (SIPos m)) $   -- abs (pos m + neg n) = pos n + pos m
        gcastWith (addComm (SIPos n) (SIPos m)) $   -- abs (pos m + neg n) = pos m + pos n
        absTriangle (SIPos m) (SINeg n)

intAdd2PosAbs :: SNat n -> SNat m -> Abs (IPos n + IPos m) :~: IPos n + IPos m
intAdd2PosAbs n m = gcastWith (addPos3 n m) Refl

intAdd2NegAbs :: SNat n -> SNat m -> Abs (INeg n + INeg m) :~: IPos n + IPos m
intAdd2NegAbs n m = gcastWith (addPos3 n m) $ gcastWith (addNeg3 n m) Refl
