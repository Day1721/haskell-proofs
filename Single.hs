{-# LANGUAGE    DataKinds
  ,             TypeFamilies
  ,             TypeFamilyDependencies
  ,             UndecidableInstances
  #-}

module Single where

import Data.Kind
import Data.Type.Equality
import Data.Void

import Unsafe.Coerce

class Single k where
    type Sing (a :: k) = r | r -> a
    type Desing k = r | r -> k
    fromSing :: Sing (a :: k) -> Desing k
    withSing :: Desing k -> (forall a. Sing (a :: k) -> r) -> r


class Single k => EqDec k where
    (=?=) :: Sing (a :: k) -> Sing (b :: k) -> Either (a :~: b) (a :~: b -> Void)


type a ~> b = (a, b) -> Type
infixr 0 ~>
type family Apply (f :: a ~> b) (x :: a) :: b
type f @@ x = Apply f x
infixl 8 @@

-- class SFun (f :: a ~> b) where
--     sFun :: Sing (v :: a) -> Sing (f @@ v)

data SFunction (f :: a ~> b) = SFunction {
    applyFunc :: forall (x :: a). Sing x -> Sing (f @@ x)
}
(@@) :: SFunction (f :: a ~> b) -> Sing (x :: a) -> Sing (f @@ x)
(@@) f = applyFunc f

instance (Single a, Single b) => Single (a ~> b) where
    type Sing f = SFunction f
    type Desing (a ~> b) = Desing a -> Desing b
    fromSing sf x = withSing x $ fromSing . applyFunc sf
    withSing (vf :: Desing a -> Desing b) (f :: forall (f :: a ~> b). SFunction f -> r) = f $ SFunction { applyFunc = \sa -> withSing (vf $ fromSing sa) cast} where
        cast :: Sing (x :: b) -> Sing (y :: b)
        cast = unsafeCoerce

applyEqFunc :: Sing n -> SFunction f -> SFunction g -> f :~: g -> f @@ n :~: g @@ n
applyEqFunc _ _ _ Refl = Refl

funcEqCoerse :: SFunction f -> SFunction g -> (forall x. Sing x -> f @@ x :~: g @@ x) -> f :~: g
funcEqCoerse f g p = unsafeCoerce Refl

-- Id :: a -> a
type F_Id = F_Id0
data F_Id0 :: a ~> a
type F_Id1 x = x
type instance Apply F_Id0 x = F_Id1 x
f_Id :: SFunction F_Id0
f_Id = SFunction { applyFunc = \x -> x }

-- Const :: a -> b -> a
type F_Const = F_Const0
data F_Const0 :: a ~> b ~> a
data F_Const1 x :: b ~> a
type F_Const2 x y = x
type instance Apply F_Const0 x = F_Const1 x
type instance Apply (F_Const1 x) y = F_Const2 x y
f_Const = SFunction { applyFunc = \x -> f_Const1 x } :: SFunction F_Const
f_Const1 :: Sing (x :: a) -> forall b. SFunction (F_Const1 x :: b ~> a)
f_Const1 sx = SFunction { applyFunc = \_ -> sx }

-- f_Const1 :: Sing a -> SFunction (F_Const1 a)
-- f_Const1 (x :: Sing a) = SFunction foo where
--     foo :: Sing b -> Sing (F_Const1 a @@ b) 
--     foo b = x

-- Compose :: (a -> b) -> (b -> c) -> a -> c
type F_Compose = F_Compose0
data F_Compose0 :: (b ~> c) ~> (a ~> b) ~> a ~> c
data F_Compose1 (f :: b ~> c) :: (a ~> b) ~> a ~> c
data F_Compose2 (f :: b ~> c) (g :: a ~> b) :: a ~> c
type F_Compose3 f g x = f @@ (g @@ x)
type instance Apply  F_Compose0 f = F_Compose1 f
type instance Apply (F_Compose1 f) g = F_Compose2 f g
type instance Apply (F_Compose2 f g) x = F_Compose3 f g x
f_Compose :: SFunction F_Compose
f_Compose = SFunction { applyFunc = f_Compose1 }
f_Compose1 :: SFunction f -> SFunction (F_Compose1 f)
f_Compose1 f = SFunction { applyFunc = f_Compose2 f }
f_Compose2 :: SFunction f -> SFunction g -> SFunction (F_Compose2 f g)
f_Compose2 f g = SFunction { applyFunc = \x -> f @@ (g @@ x) }


type F_SApply = F_SApply0
data F_SApply0 :: (a ~> b ~> c) ~> (a ~> b) ~> a ~> c
data F_SApply1 (x :: a ~> b ~> c) :: (a ~> b) ~> a ~> c
data F_SApply2 (x :: a ~> b ~> c) (y :: a ~> b) :: a ~> c
type F_SApply3 x y z = x @@ z @@ (y @@ z)
type instance Apply F_SApply0 x = F_SApply1 x
type instance Apply (F_SApply1 x) y = F_SApply2 x y
type instance Apply (F_SApply2 x y) z = F_SApply3 x y z
f_SApply :: SFunction F_SApply
f_SApply = SFunction { applyFunc = f_SApply1 }
f_SApply1 :: SFunction x -> SFunction (F_SApply1 x)
f_SApply1 x = SFunction { applyFunc = f_SApply2 x }
f_SApply2 :: SFunction x -> SFunction y -> SFunction (F_SApply2 x y)
f_SApply2 x y = SFunction { applyFunc = \z -> x @@ z @@ (y @@ z) }


type F_Flip = F_Flip0
data F_Flip0 :: (a ~> b ~> c) ~> b ~> a ~> c
data F_Flip1 (f :: a ~> b ~> c) :: b ~> a ~> c
data F_Flip2 (f :: a ~> b ~> c) (y :: b) :: a ~> c
type F_Flip3 f y x = f @@ x @@ y
type instance Apply F_Flip0 f = F_Flip1 f
type instance Apply (F_Flip1 f) y = F_Flip2 f y
type instance Apply (F_Flip2 f y) x = F_Flip3 f y x
f_Flip :: SFunction F_Flip
f_Flip = SFunction { applyFunc = f_Flip1 }
f_Flip1 :: Sing f -> SFunction (F_Flip @@ f)
f_Flip1 f = SFunction { applyFunc = f_Flip2 f }
f_Flip2 :: SFunction f -> Sing y -> SFunction (F_Flip @@ f @@ y)
f_Flip2 f y = SFunction {applyFunc = \x -> f @@ x @@ y}

flipTwiceSame :: SFunction f -> f :~: F_Flip @@ (F_Flip @@ f)
flipTwiceSame f = funcEqCoerse f (f_Flip @@ (f_Flip @@ f)) $ \x ->
    funcEqCoerse (f @@ x) (f_Flip @@ (f_Flip @@ f) @@ x) $ const Refl