module Haskell.Law.MonadPlus.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Eq
open import Haskell.Prim.Maybe

open import Haskell.Prim.Monad
open import Haskell.Prim.MonadPlus

open import Haskell.Law.MonadPlus.Def
open import Haskell.Law.Monad.Maybe

--------------------------------------------------
-- IsLawfulMonadPlus

instance
  iLawfulMonadPlusMaybe : IsLawfulMonadPlus Maybe
  iLawfulMonadPlusMaybe .mplus-mzero-x Nothing = refl
  iLawfulMonadPlusMaybe .mplus-mzero-x (Just x) = refl

  iLawfulMonadPlusMaybe .mplus-x-mzero Nothing = refl
  iLawfulMonadPlusMaybe .mplus-x-mzero (Just x) = refl

  iLawfulMonadPlusMaybe .mplus-assoc Nothing y z = refl
  iLawfulMonadPlusMaybe .mplus-assoc (Just x) y z = refl

  iLawfulMonadPlusMaybe .mzero-bind k = refl

  iLawfulMonadPlusMaybe .bind-mzero Nothing  = refl
  iLawfulMonadPlusMaybe .bind-mzero (Just x) = refl

--------------------------------------------------
-- IsDistributiveMonadPlus

¬-IsDistributMonadPlusMaybe : IsDistributiveMonadPlus Maybe → ⊥
¬-IsDistributMonadPlusMaybe (record {mplus-bind = mplus-bind}) =
    case mplus-bind (Just 1) (Just 2) k of λ ()
  where
    k : Nat → Maybe Nat
    k x = if x == 1 then Nothing else Just x
