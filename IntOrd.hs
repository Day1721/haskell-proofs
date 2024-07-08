{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module IntOrd where
import           Data.Type.Equality
import           Int
import           IntAdd
import           Nat
import           Ops
import           Prelude            hiding (Int)
import           Single

data IntNatEx i where
    IntNatEx :: SNat n -> IntNatEx (N2I n)

instance PartOrd Int where
    type i <= j = IntNatEx (j - i)
    leRefl i = case addInvZR i of { Refl -> IntNatEx SZ }
    leAsym i j (IntNatEx SZ) _                      = groupSubZEq i j Refl
    leAsym i j _ (IntNatEx SZ)                      = sym $ groupSubZEq j i Refl
    leAsym i j (IntNatEx (SS ilej)) (IntNatEx (SS jlei)) =case eq of {} where
        eq = trans (sym $ addPos3 jlei ilej) $                                      -- pos (S n + m) = pos n + pos m = (i - j) + (j - i)
            trans (singApplyF (f_Add @@ (i .-. j)) $ sym $ groupInvSubSwap i j) $   -- pos (S n + m) = (i - j) + inv (i - j)
            addInvZR (i .-. j)                                                      -- pos (S n + m) = 0
    leTrans i j k (IntNatEx SZ) jlek = case groupSubZEq i j Refl of { Refl -> jlek }
    leTrans i j k ilej (IntNatEx SZ) = case groupSubZEq j k Refl of { Refl -> ilej }
    leTrans i j k (IntNatEx (SS ilej)) (IntNatEx (SS jlek)) = case eq of {Refl -> IntNatEx $ SS $ SS $ jlek .+. ilej} where
        eq = trans (sym $ addPos3 jlek ilej) $                          -- pos (S m + n) = pos m + pos n = (k - j) + (j - i) = (k + inv j) + (j + inv i)
            trans (sym $ addAssoc k (addInv j) (j .-. i)) $             -- pos (S m + n) = k + (inv j + (j + inv i))
            singApplyF (f_Add @@ k) $
                trans (addAssoc (addInv j) j (addInv i)) $                          -- pos (S m + n) = k + ((inv j + j) + inv i)
                trans (singApplyF (f_Flip @@ f_Add @@ addInv i) $ addInvZL j) $     -- pos (S m + n) = k + (0 + inv i)
                addZeroL $ addInv i                                                 -- pos (S m + n) = k - i

intNatLePos :: SNat n -> SNat m -> n <= m -> IPos n <= IPos m
intNatLePos n m le = case natLeDiff n m le of
    LeDiffEx k Refl -> case k of
        SZ    -> castWith (apply Refl $ sym $ addInvZR (SIPos m)) $ IntNatEx k
        SS k' -> castWith (apply Refl $ sym $                                           -- pos (S k' + n) + neg n = pos k'
                trans (singApplyF (f_Flip @@ f_Add @@ SINeg n) $ sym $ addPos3 k' n) $  -- (pos k' + pos n) + neg n = pos k'
                trans (sym $ addAssoc (SIPos k') (SIPos n) (SINeg n)) $                 -- pos k' + (pos n + neg n) = pos k'
                flip trans (addZeroR $ SIPos k') $                                      -- pos k' + (pos n + neg n) = pos k' + 0
                singApplyF (f_Add @@ SIPos k') $ addInvZR (SIPos n)
            ) $ IntNatEx k

intNatLeNeg :: SNat n -> SNat m -> n <= m -> INeg m <= INeg n
intNatLeNeg n m le = case natLeDiff n m le of
    LeDiffEx k Refl -> case k of
        SZ    -> castWith (apply Refl $ sym $ addInvZL (SIPos m)) $ IntNatEx k
        SS k' -> castWith (apply Refl $ sym $                                           -- neg n + pos (S k' + n) = pos k'
                trans (addComm (SINeg n) (SIPos m)) $                                   -- pos (S k' + n) + neg n = pos k'
                trans (singApplyF (f_Flip @@ f_Add @@ SINeg n) $ sym $ addPos3 k' n) $  -- (pos k' + pos n) + neg n = pos k'
                trans (sym $ addAssoc (SIPos k') (SIPos n) (SINeg n)) $                 -- pos k' + (pos n + neg n) = pos k'
                flip trans (addZeroR $ SIPos k') $                                      -- pos k' + (pos n + neg n) = pos k' + 0
                singApplyF (f_Add @@ SIPos k') $ addInvZR (SIPos n)
            ) $ IntNatEx k

instance TotalOrd Int where
    leDec SIZ SIZ       = Left $ IntNatEx SZ
    leDec (SIPos n) SIZ = Right $ castWith (apply Refl $ intAddRPos SIZ n) $ IntNatEx $ SS n
    leDec (SINeg n) SIZ = Left $ IntNatEx $ SS n
    leDec SIZ n = either Right Left $ leDec n SIZ
    leDec (SIPos n) (SIPos m) = case leDec n m of
        Left nlem  -> Left $ intNatLePos n m nlem
        Right mlen -> Right $ intNatLePos m n mlen
    leDec (SINeg n) (SINeg m) = case leDec n m of
        Left nlem  -> Right $ intNatLeNeg n m nlem
        Right mlen -> Left $ intNatLeNeg m n mlen
    leDec (SIPos n) (SINeg m) = Right $ castWith (apply Refl $ sym $ addPos3 n m) $ IntNatEx (SS $ SS n .+. m)
    leDec (SINeg n) (SIPos m) = Left $ castWith (apply Refl $ sym $ addPos3 m n) $ IntNatEx (SS $ SS m .+. n)
