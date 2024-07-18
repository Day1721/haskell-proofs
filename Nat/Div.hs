{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Nat.Div where

import           Add
import           Data.Type.Equality
import           Mul
import           Nat.Add
import           Nat.Defs
import           Nat.Mul
import           Nat.Ord
import           Ops

data NatDivides n m where
    NatDivides :: SNat k -> k * n :~: m -> NatDivides n m


natDiv1 :: SNat n -> NatDivides N1 n
natDiv1 n = NatDivides n $ trans (mulComm n n1) $ addZeroR n

natDivN :: SNat n -> NatDivides n n
natDivN n = NatDivides n1 $ addZeroR n

natDivZ :: SNat n -> NatDivides n Z
natDivZ n = NatDivides SZ Refl

natDivLe :: SNat n -> SNat m -> NatDivides n m -> Either (m :~: Z) (n <= m)
natDivLe n m (NatDivides k eq) = case k of
    SZ    -> Left $ sym eq
    SS k' -> Right $ gcastWith eq $ natNLeNKL n k'

type NatPrime (n :: Nat) = forall m. SNat m -> NatDivides m n -> Either (m :~: n) (m :~: N1)

n2Prime :: NatPrime N2
n2Prime m div@(NatDivides k eq) = let Right le = natDivLe m n2 div in case m of
    SZ        -> case trans (sym $ natMulZ k) eq of {}
    SS SZ     -> Right Refl
    SS (SS m) -> let eq' = natLeDown m SZ $ natLeDown (SS m) n1 le in Left $ gcastWith (natLeZEqZ m eq') Refl
