{-# LANGUAGE NoStarIsType           #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Ops where

import           Add
import           Data.Kind
import           Data.Type.Equality
import           Mul
import           Ord
import           Single

class (PartOrd t, AddMonoid t) => Absolute t where
    type Abs (a :: t) :: t
    abs :: Sing (a :: t) -> Sing (Abs a)
    absGeZ :: Sing (a :: t) -> AddZero <= Abs a
    absZIffZ :: Sing (a :: t) -> Abs a :~: AddZero -> a :~: AddZero
    absMul :: Sing (a :: t) -> Sing b -> Abs (a * b) :~: Abs a * Abs b
    absTriangle :: Sing (a :: t) -> Sing b -> Abs (a + b) <= Abs a + Abs b

class Single t => Divides t where
    type family (||) (a :: t) (b :: t) :: Type
    type family (|/|) (a :: t) (b :: t) :: Type
    divDec :: Sing @t a -> Sing b -> Either (a || b) (a |/| b)
