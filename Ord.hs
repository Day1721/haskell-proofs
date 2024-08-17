{-# LANGUAGE TypeFamilies #-}
module Ord where
import           Data.Data
import           Single

class Single t => PartOrd t where
    type family (<=) (a :: t) (b :: t)
    leRefl :: Sing (a :: t) -> a <= a
    leAsym :: Sing (a :: t) -> Sing b -> a <= b -> b <= a -> a :~: b
    leTrans :: Sing (a :: t) -> Sing b -> Sing c -> a <= b -> b <= c -> a <= c
infix 4 <=

type (>=) a b = (<=) b a
infix 4 >=

class PartOrd t => TotalOrd t where
    leDec :: Sing @t a -> Sing b -> Either (a <= b) (b <= a)

class Single t => StrictPartOrd t where
    type (<) (a :: t) (b :: t)
    ltNRefl :: Sing @t a -> Not (a < a)
    ltAsym :: Sing @t a -> Sing b -> a < b -> Not (b < a)
    ltTrans :: Sing @t a -> Sing b -> Sing c -> a < b -> b < c -> a < c
infix 4 <

type (>) a b = (<) b a
infix 4 >

class (PartOrd t, StrictPartOrd t) => FullPartOrd t where
    le2lt :: Sing @t a -> Sing b -> a <= b -> Either (a :~: b) (a < b)
    lt2le :: Sing @t a -> Sing b -> a < b -> a <= b

data StrictOrdering a b = SO_LT (a < b) | SO_EQ (a :~: b) | SO_GT (a > b)

class StrictPartOrd t => TotalStrictOrd t where
    ltDec :: Sing @t a -> Sing b -> StrictOrdering a b


type TotalFullOrd t = (FullPartOrd t, TotalOrd t, TotalStrictOrd t)
