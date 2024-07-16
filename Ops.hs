{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}

module Ops where

import           Add
import           Data.Type.Equality
import           Mul
import           Single

class Single t => PartOrd t where
    type family (<=) (a :: t) (b :: t)
    leRefl :: Sing (a :: t) -> a <= a
    leAsym :: Sing (a :: t) -> Sing b -> a <= b -> b <= a -> a :~: b
    leTrans :: Sing (a :: t) -> Sing b -> Sing c -> a <= b -> b <= c -> a <= c
infix 4 <=

class PartOrd t => TotalOrd t where
    leDec :: Sing (a :: t) -> Sing b -> Either (a <= b) (b <= a)


class (PartOrd t, AddMonoid t) => Absolute t where
    type Abs (a :: t) :: t
    abs :: Sing (a :: t) -> Sing (Abs a)
    absGeZ :: Sing (a :: t) -> AddZero <= Abs a
    absZIffZ :: Sing (a :: t) -> Abs a :~: AddZero -> a :~: AddZero
    absMul :: Sing (a :: t) -> Sing b -> Abs (a * b) :~: Abs a * Abs b
    absTriangle :: Sing (a :: t) -> Sing b -> Abs (a + b) <= Abs a + Abs b
