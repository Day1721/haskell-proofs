{-# LANGUAGE    DataKinds
  ,             TypeFamilies
  ,             NoStarIsType
  #-}
module Ops where

import Single

class Single k => Add k where
    type family (+) (a :: k) (b :: k) :: k 
    (.+.) :: Sing (a :: k) -> Sing (b :: k) -> Sing (a + b)
infixl 6 +

type F_Add = F_Add0
data F_Add0 :: k ~> k ~> k
data F_Add1 (a :: k) :: k ~> k
type F_Add2 a b = a + b
type instance Apply F_Add0 a = F_Add1 a
type instance Apply (F_Add1 a) b = F_Add2 a b

f_Add :: Add k => SFunction (F_Add :: k ~> k ~> k)
f_Add = SFunction { applyFunc = f_Add1 }
f_Add1 :: Add k => Sing (n :: k) -> SFunction (F_Add1 n)
f_Add1 n = SFunction { applyFunc = (n .+.) }



class Single k => Mul k where
    type family (*) (a :: k) (b :: k) :: k 
    (.*.) :: Sing (a :: k) -> Sing (b :: k) -> Sing (a * b)
infixl 7 *

type Sum :: forall k. (k ~> k) -> k -> k
type family Sum f max

type F_Mul = F_Mul0
data F_Mul0 :: k ~> k ~> k
data F_Mul1 (a :: k) :: k ~> k
type F_Mul2 a b = a * b
type instance Apply F_Mul0 a = F_Mul1 a
type instance Apply (F_Mul1 a) b = F_Mul2 a b

f_Mul1 :: Mul k => Sing (n :: k) -> SFunction (F_Mul1 n)
f_Mul1 n = SFunction { applyFunc = (n .*.) }
