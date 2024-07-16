{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
module PointwiseFuncOps where

import           Add
import           Data.Type.Equality
import           Ops
import           SFuncUnsafe
import           Single

instance (Add k, Single l) => Add (l ~> k) where
    type f + g = F_SApply @@ (F_Compose @@ F_Add @@ f) @@ g
    f .+. g = f_SApply @@ (f_Compose @@ f_Add @@ f) @@ g

funAddApplySwap :: Add a => SFunction (f :: a ~> a) -> SFunction g -> Sing n -> (f + g) @@ n :~: f @@ n + g @@ n
funAddApplySwap f g n = Refl

instance (AddMonoid t, Single l) => AddMonoid (l ~> t) where
    addAssoc f g h = funcEqCoerse (f .+. (g .+. h)) ((f .+. g) .+. h) $ \x -> addAssoc (f @@ x) (g @@ x) (h @@ x)
    type AddZero = F_Const @@ AddZero
    addZero = f_Const @@ addZero
    addZeroL f = funcEqCoerse (addZero .+. f) f $ \x -> addZeroL (f @@ x)
    addZeroR f = funcEqCoerse (f .+. addZero) f $ \x -> addZeroR (f @@ x)

instance (AddGroup t, Single l) => AddGroup (l ~> t) where
    type AddInv f = F_Compose @@ F_AddInv @@ f
    addInv f = f_Compose @@ f_AddInv @@ f
    addInvZL f = funcEqCoerse (addInv f .+. f) addZero $ \x -> addInvZL (f @@ x)
    addInvZR = addInvZLtoR addAssoc addZero f_AddInv addZeroL addInvZL


instance (AddComm t, Single l) => AddComm (l ~> t) where
  addComm f g = funcEqCoerse (f .+. g) (g .+. f) $ \x -> addComm (f @@ x) (g @@ x)
