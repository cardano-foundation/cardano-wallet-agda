{-# OPTIONS --erasure #-}

module Data.Function.Law
    {-|
    ; prop-==-Injective
    -}
    where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Def public using (Injective)

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

dummy :: ()
dummy = ()
#-}

-- | Injective functions preserve equality.
prop-==-Injective
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
  → ∀ (f : a → b) → Injective f
  → ∀ (x y : a)
  → (x == y)
    ≡ (f x == f y)
--
prop-==-Injective f inj x y
  with f x == f y in eqf
... | True  = equality' _ _ (inj (equality _ _ eqf))
... | False = nequality' _ _ (nequality (f x) (f y) eqf ∘ cong f)
