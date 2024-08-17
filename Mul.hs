{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Mul where

import           Add
import           Data.Type.Equality
import           Single

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
f_Mul :: Mul t => SFunction (F_Mul :: t ~> t ~> t)
f_Mul = SFunction {applyFunc = f_Mul1}
f_Mul1 :: Mul t => Sing (n :: t) -> SFunction (F_Mul1 n)
f_Mul1 n = SFunction { applyFunc = (n .*.) }

type MulL a = F_Mul @@ a
mulL :: Mul t => Sing (a :: t) -> SFunction (MulL a)
mulL = applyFunc f_Mul
type MulR a = F_Flip @@ F_Mul @@ a
mulR :: Mul t => Sing (a :: t) -> SFunction (MulR a)
mulR = applyFunc $ f_Flip @@ f_Mul


class Mul t => MulMonoid t where
    mulAssoc :: Sing @t a -> Sing b -> Sing c -> a * (b * c) :~: (a * b) * c
    type MulOne :: t
    mulOneL :: Sing @t a -> MulOne * a :~: a
    mulOneR :: Sing @t a -> a * MulOne :~: a


class Mul t => MulComm t where
    mulComm :: Sing @t a -> Sing b -> a * b :~: b * a

type MulAbelMonoid t = (MulMonoid t, MulComm t)

groupMul4SwapInner :: MulAbelMonoid t => Sing @t a -> Sing b -> Sing c -> Sing d -> (a * b) * (c * d) :~: (a * c) * (b * d)
groupMul4SwapInner a b c d =                    -- (a * b) * (c * d) = (a * c) * (b * d)
    trans (sym $ mulAssoc a b (c .*. d)) $      -- a * (b * (c * d)) = (a * c) * (b * d)
    trans (singApplyF (f_Mul @@ a) $                                -- b * (c * d) = c * (b * d)
        trans (mulAssoc b c d) $                                    -- (b * c) * d = c * (b * d)
        trans (singApplyF (f_Flip @@ f_Mul @@ d) $ mulComm b c) $   -- (c * d) * d = c * (b * d)
        sym $ mulAssoc c b d
    ) $                                         -- a * (c * (b * d)) = (a * c) * (b * d)
    mulAssoc a c $ b .*. d

class (AddMonoid t, MulMonoid t) => AddMulRingBase t where
    addMulDistL :: Sing @t a -> Sing b -> Sing c -> c * (a + b) :~: c * a + c * b
    addMulDistR :: Sing @t a -> Sing b -> Sing c -> (a + b) * c :~: a * c + b * c

type AddMulSemiRing t = (AddAbelMonoid t, AddMulRingBase t)
type AddMulNearRing t = (AddGroup t, AddMulRingBase t)
type AddMulRing t = (AddAbelGroup t, AddMulRingBase t)


class Single t => Pow t where
    type family (^) (a :: t) (b :: t) :: t
    (.^.) :: Sing @t a -> Sing b -> Sing (a ^ b)
infixl 8 ^
infixl 8 .^.

type F_Pow = F_Pow0
data F_Pow0 :: t ~> t ~> t
data F_Pow1 (a :: t) :: t ~> t
type F_Pow2 a b = a ^ b
type instance Apply F_Pow0 a = F_Pow1 a
type instance Apply (F_Pow1 a) b = F_Pow2 a b
f_Pow :: Pow t => SFunction (F_Pow :: t ~> t ~> t)
f_Pow = SFunction {applyFunc = f_Pow1}
f_Pow1 :: Pow t => Sing (n :: t) -> SFunction (F_Pow1 n)
f_Pow1 n = SFunction { applyFunc = (n .^.) }
