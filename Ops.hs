{-# LANGUAGE    DataKinds
  ,             TypeFamilies
  ,             NoStarIsType
  ,             UndecidableInstances
  #-}
module Ops where

import Data.Type.Equality
import Single

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
