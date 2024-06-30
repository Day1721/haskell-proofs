{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Ops where

import           Data.Type.Equality
import           Single

class Single t => Add t where
    type family (+) (a :: t) (b :: t) :: t
    (.+.) :: Sing (a :: t) -> Sing (b :: t) -> Sing (a + b)
infixl 6 +
infixl 6 .+.

type F_Add = F_Add0
data F_Add0 :: t ~> t ~> t
data F_Add1 (a :: t) :: t ~> t
type F_Add2 a b = a + b
type instance Apply F_Add0 a = F_Add1 a
type instance Apply (F_Add1 a) b = F_Add2 a b

f_Add :: Add t => SFunction (F_Add :: t ~> t ~> t)
f_Add = SFunction { applyFunc = f_Add1 }
f_Add1 :: Add t => Sing (n :: t) -> SFunction (F_Add1 n)
f_Add1 n = SFunction { applyFunc = (n .+.) }

instance (Add k, Single l) => Add (l ~> k) where
    type f + g = F_SApply @@ (F_Compose @@ F_Add @@ f) @@ g
    f .+. g = f_SApply @@ (f_Compose @@ f_Add @@ f) @@ g

funAddApplySwap :: Add a => SFunction (f :: a ~> a) -> SFunction g -> Sing n -> (f + g) @@ n :~: f @@ n + g @@ n
funAddApplySwap f g n = Refl

addSameL :: Add t => Sing (k :: t) -> forall n m. n :~: m -> k + n :~: k + m
addSameL _ Refl = Refl
addSameLX :: Add t => Sing (k :: t) -> Sing n -> Sing m -> n :~: m -> k + n :~: k + m
addSameLX _ _ _ Refl = Refl

addSameR :: Add t => Sing (k :: t) -> forall n m. n :~: m -> n + k :~: m + k
addSameR _ Refl = Refl
addSameRX :: Add t => Sing (k :: t) -> Sing n -> Sing m -> n :~: m -> n + k :~: m + k
addSameRX _ _ _ Refl = Refl

addBothSame :: Add t => forall (n :: t) m. n :~: m -> forall k l. k :~: l -> n + k :~: m + l
addBothSame Refl Refl = Refl
addBothSameX :: Add t => Sing (n :: t) -> Sing k -> Sing m -> Sing l -> n :~: m -> k :~: l -> n + k :~: m + l
addBothSameX _ _ _ _ Refl Refl = Refl

class Add t => AddMonoid t where
    addAssoc :: Sing (n :: t) -> Sing m -> Sing l -> n + (m + l) :~: (n + m) + l
    type family AddZero :: t
    addZero :: Sing (AddZero :: t)
    addZeroL :: Sing (n :: t) -> AddZero + n :~: n
    addZeroR :: Sing (n :: t) -> n + AddZero :~: n

instance (AddMonoid t, Single l) => AddMonoid (l ~> t) where
    addAssoc f g h = funcEqCoerse (f .+. (g .+. h)) ((f .+. g) .+. h) $ \x -> addAssoc (f @@ x) (g @@ x) (h @@ x)
    type AddZero = F_Const @@ AddZero
    addZero = f_Const @@ addZero
    addZeroL f = funcEqCoerse (addZero .+. f) f $ \x -> addZeroL (f @@ x)
    addZeroR f = funcEqCoerse (f .+. addZero) f $ \x -> addZeroR (f @@ x)


class Add t => AddComm t where
  addComm :: Sing (n :: t) -> Sing (m :: t) -> n + m :~: m + n

instance (AddComm t, Single l) => AddComm (l ~> t) where
  addComm f g = funcEqCoerse (f .+. g) (g .+. f) $ \x -> addComm (f @@ x) (g @@ x)

addFlipL :: (AddComm t, AddMonoid t) => Sing (n :: t) -> Sing m -> Sing k -> n + (m + k) :~: m + (n + k)
addFlipL n m k =
    trans (addAssoc n m k) $
    flip trans (sym $ addAssoc m n k) $
    addSameR k $
    addComm n m

class AddMonoid t => AddGroup t where
    type AddInv (a :: t) :: t
    addInv :: Sing (a :: t) -> Sing (AddInv a)
    addInvZL :: Sing (a :: t) -> AddInv a + a :~: AddZero
    addInvZR :: Sing (a :: t) -> a + AddInv a :~: AddZero


class Single t => Mul t where
    type family (*) (a :: t) (b :: t) :: t
    (.*.) :: Sing (a :: t) -> Sing (b :: t) -> Sing (a * b)
infixl 7 *
infixl 7 .*.

type F_Mul = F_Mul0
data F_Mul0 :: t ~> t ~> t
data F_Mul1 (a :: t) :: t ~> t
type F_Mul2 a b = a * b
type instance Apply F_Mul0 a = F_Mul1 a
type instance Apply (F_Mul1 a) b = F_Mul2 a b

f_Mul1 :: Mul t => Sing (n :: t) -> SFunction (F_Mul1 n)
f_Mul1 n = SFunction { applyFunc = (n .*.) }



class Single t => PartOrd t where
    data family (<=) (a :: t) (b :: t)
    leRefl :: Sing (a :: t) -> a <= a
    leAsym :: Sing (a :: t) -> Sing b -> a <= b -> b <= a -> a :~: b
    leTrans :: Sing (a :: t) -> Sing b -> Sing c -> a <= b -> b <= c -> a <= c
infix 4 <=

instance (PartOrd t, Single l) => PartOrd (l ~> t) where
    data (<=) f g = FuncLe (forall x. Sing x -> f @@ x <= g @@ x)
    leRefl f = FuncLe $ \x -> leRefl (f @@ x)
    leAsym f g (FuncLe fleg) (FuncLe glef) = funcEqCoerse f g $ \x -> leAsym (f @@ x) (g @@ x) (fleg x) (glef x)
    leTrans f g h (FuncLe fleg) (FuncLe gleh) = FuncLe $ \x -> leTrans (f @@ x) (g @@ x) (h @@ x) (fleg x) (gleh x)

class PartOrd t => TotalOrd t where
    leDec :: Sing (a :: t) -> Sing b -> Either (a <= b) (b <= a)




class Single n => Sub n where
    type (-) (a :: n) (b :: n) :: n
    (.-.) :: Sing (a :: n) -> Sing b -> Sing (a - b)
infixl 6 -
infixl 6 .-.

type F_Sub = F_Sub0
data F_Sub0 :: t ~> t ~> t
data F_Sub1 (a :: t) :: t ~> t
type F_Sub2 a b = a - b
type instance Apply F_Sub0 a = F_Sub1 a
type instance Apply (F_Sub1 a) b = F_Sub2 a b

f_Sub :: Sub t => SFunction (F_Sub :: t ~> t ~> t)
f_Sub = SFunction { applyFunc = f_Sub1 }
f_Sub1 :: Sub t => Sing (n :: t) -> SFunction (F_Sub1 n)
f_Sub1 n = SFunction { applyFunc = (n .-.) }

instance (Sub k, Single l) => Sub (l ~> k) where
    type f - g = F_SApply @@ (F_Compose @@ F_Sub @@ f) @@ g
    f .-. g = f_SApply @@ (f_Compose @@ f_Sub @@ f) @@ g
