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

type AddAssoc t = forall (a :: t) b c. Sing a -> Sing b -> Sing c -> a + (b + c) :~: (a + b) + c
type AddZeroL t (z :: t) = forall a. Sing a -> z + a :~: a
type AddZeroR t (z :: t) = forall a. Sing a -> a + z :~: a

class Add t => AddMonoid t where
    addAssoc :: AddAssoc t
    type family AddZero :: t
    addZero :: Sing (AddZero :: t)
    addZeroL :: AddZeroL t AddZero
    addZeroR :: AddZeroR t AddZero

addFlipL :: (AddComm t, AddMonoid t) => Sing (n :: t) -> Sing m -> Sing k -> n + (m + k) :~: m + (n + k)
addFlipL n m k =
    trans (addAssoc n m k) $
    flip trans (sym $ addAssoc m n k) $
    addSameR k $
    addComm n m


type AddInvZL t (inv :: t ~> t) z = forall a. Sing a -> inv @@ a + a :~: z
type AddInvZR t (inv :: t ~> t) z = forall a. Sing a -> a + inv @@ a :~: z

addInvZLtoR :: Add t => AddAssoc t -> Sing (z :: t) -> SFunction (inv :: t ~> t) -> AddZeroL t z -> AddInvZL t inv z -> AddInvZR t inv z
addInvZLtoR assoc z inv zeroL invL a =                       -- a + inv a = z
    trans (sym $ zeroL $ a .+. inv @@ a) $                  -- z + (a + inv a) = z
    trans (
        singApplyF (f_Flip @@ f_Add @@ (a .+. inv @@ a)) $  -- z = inv (inv a) + inv a
        sym $ invL (inv @@ a)
    ) $                                                     -- (inv (inv a) + inv a) + (a + inv a) = z
    trans (
        sym $ assoc (inv @@ (inv @@ a)) (inv @@ a) $ a .+. inv @@ a
    ) $                                                     -- inv (inv a) + (inv a + (a + inv a)) = z
    trans (
        singApplyF (f_Add @@ (inv @@ (inv @@ a))) $             -- inv a + (a + inv a) = inv a
        trans (assoc (inv @@ a) a (inv @@ a)) $                 -- (inv a + a) + inv a = inv a
        trans (
            singApplyF (f_Flip @@ f_Add @@ (inv @@ a)) $ invL a
        ) $ zeroL $ inv @@ a
    ) $                                                     -- inv (inv a) + inv a = z
    invL $ inv @@ a
addInvZRtoL :: Add t => AddAssoc t -> Sing (z :: t) -> SFunction (inv :: t ~> t) -> AddZeroR t z -> AddInvZR t inv z -> AddInvZL t inv z
addInvZRtoL assoc z inv zeroR invR a =                       -- inv a + a = z
    trans (sym $ zeroR $ inv @@ a .+. a) $                  -- (inv a + a) + z = z
    trans (
        singApplyF (f_Add @@ (inv @@ a .+. a)) $            -- z = inv a + inv (inv a)
        sym $ invR (inv @@ a)
    ) $                                                     -- (inv a + a) + (inv a + inv (inv a)) = z
    trans (
        assoc (inv @@ a .+. a) (inv @@ a) (inv @@ (inv @@ a))
    ) $                                                     -- ((inv a + a) + inv a) + inv (inv a) = z
    trans (
        singApplyF (f_Flip @@ f_Add @@ (inv @@ (inv @@ a))) $   -- (inv a + a) + inv a = inv a
        trans (sym $ assoc (inv @@ a) a (inv @@ a)) $           -- inv a + (a + inv a) = inv a
        trans (
            singApplyF (f_Add @@ (inv @@ a)) $ invR a
        ) $ zeroR $ inv @@ a
    ) $                                                     -- inv (inv a) + inv a = z
    invR $ inv @@ a

addZeroLtoR :: Add t => AddAssoc t -> Sing (z :: t) -> SFunction (inv :: t ~> t) -> AddInvZL t inv z -> AddZeroL t z -> AddZeroR t z
addZeroLtoR assoc z inv invL zeroL a =                      -- a + z = a
    let invR = addInvZLtoR assoc z inv zeroL invL in
    trans (singApplyF (f_Add @@ a) $ sym $ invL a) $        -- a + (inv a + a) = a
    trans (assoc a (inv @@ a) a) $                          -- (a + inv a) + a = a
    trans (singApplyF (f_Flip @@ f_Add @@ a) $ invR a) $    -- z + a = a
    zeroL a
addZeroRtoL :: Add t => AddAssoc t -> Sing (z :: t) -> SFunction (inv :: t ~> t) -> AddInvZR t inv z -> AddZeroR t z -> AddZeroL t z
addZeroRtoL assoc z inv invR zeroR a =                          -- z + a = a
    let invL = addInvZRtoL assoc z inv zeroR invR in
    trans (singApplyF (f_Flip @@ f_Add @@ a) $ sym $ invR a) $  -- (inv a + a) + a = a
    trans (sym $ assoc a (inv @@ a) a) $                        -- (a + inv a) + a = a
    trans (singApplyF (f_Add @@ a) $ invL a) $                  -- z + a = a
    zeroR a



class AddMonoid t => AddGroup t where
    type AddInv (a :: t) :: t
    addInv :: Sing (a :: t) -> Sing (AddInv a)
    addInvZL :: Sing (a :: t) -> AddInv a + a :~: AddZero
    addInvZL = addInvZRtoL addAssoc addZero f_AddInv addZeroR addInvZR
    addInvZR :: Sing (a :: t) -> a + AddInv a :~: AddZero
    addInvZR = addInvZLtoR addAssoc addZero f_AddInv addZeroL addInvZL
    {-# MINIMAL addInv, (addInvZL | addInvZR) #-}

type F_AddInv = F_AddInv0
data F_AddInv0 :: t ~> t
type F_AddInv1 x = AddInv x
type instance Apply F_AddInv0 x = F_AddInv1 x
f_AddInv :: AddGroup t => SFunction (F_AddInv :: t ~> t)
f_AddInv = SFunction {applyFunc = addInv}




class Add t => AddComm t where
  addComm :: Sing (n :: t) -> Sing (m :: t) -> n + m :~: m + n

groupInvLUnique :: AddGroup t => Sing (a :: t) -> Sing b -> a + b :~: AddZero -> a :~: AddInv b
groupInvLUnique a (b :: Sing b) eq =                        -- b = inv a
    trans (sym $ addZeroR a) $                              -- b + 0 = inv a
    trans (singApplyF (f_Add @@ a) $ sym $ addInvZR b) $    -- b + (a + inv a) = inv a
    trans (addAssoc a b $ addInv b) $                       -- (b + a) + inv a = inv a
    trans (singApplyF (f_Flip @@ f_Add @@ addInv b) eq) $   -- 0 + inv a = inv a
    addZeroL $ addInv b

groupInvTwiceSame :: AddGroup t => Sing (a :: t) -> AddInv (AddInv a) :~: a
groupInvTwiceSame a = sym $ groupInvLUnique a (addInv a) $ addInvZR a

groupInvAddSwap :: AddGroup t => Sing (a :: t) -> Sing b -> AddInv (a + b) :~: AddInv b + AddInv a
groupInvAddSwap a b = sym $                                     -- inv b + inv a = inv (a + b)
    groupInvLUnique (addInv b .+. addInv a) (a .+. b) $         -- (inv b + inv a) + (a + b) = 0
    trans (sym $ addAssoc (addInv b) (addInv a) (a .+. b)) $    -- inv b + (inv a + (a + b)) = 0
    flip trans (addInvZL b) $                                   -- inv b + (inv a + (a + b)) = inv b + b
    singApplyF (f_Add @@ addInv b) $                            -- inv a + (a + b) = b
    trans (addAssoc (addInv a) a b) $                           -- (inv a + a) + b = b
    flip trans (addZeroL b) $                                   -- (inv a + a) + b = 0 + b
    singApplyF (f_Flip @@ f_Add @@ b) $                         -- inv a + a = 0
    addInvZL a

type a - b = a + AddInv b
a .-. b = a .+. addInv b
infixl 6 -
infixl 6 .-.

type F_Sub = F_Sub0
data F_Sub0 :: t ~> t ~> t
data F_Sub1 (a :: t) :: t ~> t
type F_Sub2 a b = a - b
type instance Apply F_Sub0 a = F_Sub1 a
type instance Apply (F_Sub1 a) b = F_Sub2 a b

f_Sub :: AddGroup t => SFunction (F_Sub :: t ~> t ~> t)
f_Sub = SFunction { applyFunc = f_Sub1 }
f_Sub1 :: AddGroup t => Sing (n :: t) -> SFunction (F_Sub1 n)
f_Sub1 n = SFunction { applyFunc = (n .-.) }

groupInvSubSwap :: AddGroup t => Sing (a :: t) -> Sing b -> AddInv (a - b) :~: b - a
groupInvSubSwap a b =
    trans (groupInvAddSwap a $ addInv b) $
    singApplyF (f_Flip @@ f_Sub @@ a) $
    groupInvTwiceSame b

groupSubZEq :: AddGroup t => Sing (a :: t) -> Sing b -> b - a :~: AddZero -> a :~: b
groupSubZEq a b eq = sym $                                  -- b = a
    trans (sym $ addZeroR b) $                              -- b + 0 = a
    trans (singApplyF (f_Add @@ b) $ sym $ addInvZL a) $    -- b + (inv a + a) = a
    trans (addAssoc b (addInv a) a) $                       -- (b - a) + a = a
    flip trans (addZeroL a) $                               -- (b - a) + a = 0 + a
    singApplyF (f_Flip @@ f_Add @@ a) eq

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
    type family (<=) (a :: t) (b :: t)
    leRefl :: Sing (a :: t) -> a <= a
    leAsym :: Sing (a :: t) -> Sing b -> a <= b -> b <= a -> a :~: b
    leTrans :: Sing (a :: t) -> Sing b -> Sing c -> a <= b -> b <= c -> a <= c
infix 4 <=

newtype FuncLe f g = FuncLe (forall x. Sing x -> f @@ x <= g @@ x)

instance (PartOrd t, Single l) => PartOrd (l ~> t) where
    type (<=) f g = FuncLe f g
    leRefl f = FuncLe $ \x -> leRefl (f @@ x)
    leAsym f g (FuncLe fleg) (FuncLe glef) = funcEqCoerse f g $ \x -> leAsym (f @@ x) (g @@ x) (fleg x) (glef x)
    leTrans f g h (FuncLe fleg) (FuncLe gleh) = FuncLe $ \x -> leTrans (f @@ x) (g @@ x) (h @@ x) (fleg x) (gleh x)

class PartOrd t => TotalOrd t where
    leDec :: Sing (a :: t) -> Sing b -> Either (a <= b) (b <= a)



type AddAbelMonoid t = (AddMonoid t, AddComm t)
type AddAbelGroup t = (AddGroup t, AddComm t)



class (PartOrd t, AddMonoid t) => Absolute t where
    type Abs (a :: t) :: t
    abs :: Sing (a :: t) -> Sing (Abs a)
    absGeZ :: Sing (a :: t) -> AddZero <= Abs a
