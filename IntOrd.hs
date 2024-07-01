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

data IntGEZ i where
    IntGEZ_Z :: IntGEZ IZ
    IntGEZ_P :: forall n. SNat n -> IntGEZ (IPos n)

instance PartOrd Int where
    type i <= j = IntGEZ (j - i)
    leRefl i = case addInvZR i of { Refl -> IntGEZ_Z }
    leAsym i j IntGEZ_Z _                      = groupSubZEq i j Refl
    leAsym i j _ IntGEZ_Z                      = sym $ groupSubZEq j i Refl
    leAsym i j (IntGEZ_P ilej) (IntGEZ_P jlei) =case eq of {} where
        eq = trans (sym $ addPos3 jlei ilej) $                                      -- pos (S n + m) = pos n + pos m = (i - j) + (j - i)
            trans (singApplyF (f_Add @@ (i .-. j)) $ sym $ groupInvSubSwap i j) $   -- pos (S n + m) = (i - j) + inv (i - j)
            addInvZR (i .-. j)                                                      -- pos (S n + m) = 0
    leTrans i j k IntGEZ_Z jlek = case groupSubZEq i j Refl of { Refl -> jlek }
    leTrans i j k ilej IntGEZ_Z = case groupSubZEq j k Refl of { Refl -> ilej }
    leTrans i j k (IntGEZ_P ilej) (IntGEZ_P jlek) = case eq of {Refl -> IntGEZ_P $ SS $ jlek .+. ilej} where
        eq = trans (sym $ addPos3 jlek ilej) $                          -- pos (S m + n) = pos m + pos n = (k - j) + (j - i) = (k + inv j) + (j + inv i)
            trans (sym $ addAssoc k (addInv j) (j .-. i)) $             -- pos (S m + n) = k + (inv j + (j + inv i))
            singApplyF (f_Add @@ k) $
                trans (addAssoc (addInv j) j (addInv i)) $                          -- pos (S m + n) = k + ((inv j + j) + inv i)
                trans (singApplyF (f_Flip @@ f_Add @@ addInv i) $ addInvZL j) $     -- pos (S m + n) = k + (0 + inv i)
                addZeroL $ addInv i                                                 -- pos (S m + n) = k - i
