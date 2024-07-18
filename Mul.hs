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

f_Mul1 :: Mul t => Sing (n :: t) -> SFunction (F_Mul1 n)
f_Mul1 n = SFunction { applyFunc = (n .*.) }


class Mul t => MulMonoid t where
    mulAssoc :: Sing @t a -> Sing b -> Sing c -> a * (b * c) :~: (a * b) * c
    type MulOne :: t
    mulOneL :: Sing @t a -> MulOne * a :~: a
    mulOneR :: Sing @t a -> a * MulOne :~: a


class Mul t => MulComm t where
    mulComm :: Sing @t a -> Sing b -> a * b :~: b * a



class (AddAbelGroup t, MulMonoid t) => AddMulRing t where
    addMulDistL :: Sing @t a -> Sing b -> Sing c -> c * (a + b) :~: c * a + c * b
    addMulDistR :: Sing @t a -> Sing b -> Sing c -> (a + b) * c :~: a * c + b * c
