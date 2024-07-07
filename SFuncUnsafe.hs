{-# LANGUAGE TypeFamilies #-}
module SFuncUnsafe where

import           Data.Type.Equality
import           Data.Void
import           Ops
import           Single
import           Unsafe.Coerce

-- Unsafe file used by Pointwise-function classes and FuncSums
-- `funcEqCoerse` makes system unsound and should be removed
-- TODO refactor code and get rid of funcEqCoerse

funcEqCoerse :: SFunction f -> SFunction g -> (forall x. Sing x -> f @@ x :~: g @@ x) -> f :~: g
funcEqCoerse f g p = unsafeCoerce Refl

funcEqCoerseFalse :: Void
funcEqCoerseFalse = case funcEqCoerse (f_SApply @@ f_Const @@ f_Const) f_Id $ const Refl of {}


flipTwiceSame :: SFunction f -> f :~: F_Flip @@ (F_Flip @@ f)
flipTwiceSame f = funcEqCoerse f (f_Flip @@ (f_Flip @@ f)) $ \x ->
    funcEqCoerse (f @@ x) (f_Flip @@ (f_Flip @@ f) @@ x) $ const Refl

newtype FuncLe f g = FuncLe (forall x. Sing x -> f @@ x <= g @@ x)
instance (PartOrd t, Single l) => PartOrd (l ~> t) where
    type (<=) f g = FuncLe f g
    leRefl f = FuncLe $ \x -> leRefl (f @@ x)
    leAsym f g (FuncLe fleg) (FuncLe glef) = funcEqCoerse f g $ \x -> leAsym (f @@ x) (g @@ x) (fleg x) (glef x)
    leTrans f g h (FuncLe fleg) (FuncLe gleh) = FuncLe $ \x -> leTrans (f @@ x) (g @@ x) (h @@ x) (fleg x) (gleh x)
