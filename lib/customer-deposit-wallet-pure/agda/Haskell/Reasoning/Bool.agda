{-# OPTIONS --erasure #-}

module Haskell.Reasoning.Bool where

open import Haskell.Prelude
open import Haskell.Reasoning.Core

{-----------------------------------------------------------------------------
    Relate (≡ True) to logical connectives
------------------------------------------------------------------------------}

-- Logical conjunction
prop-&&-⋀
  : ∀ {x y : Bool}
  → (x && y) ≡ True
  → (x ≡ True) ⋀ (y ≡ True)
--
prop-&&-⋀ {True} {True} refl = refl `and` refl

--
prop-⋀-&&
  : ∀ {x y : Bool}
  → (x ≡ True) ⋀ (y ≡ True)
  → (x && y) ≡ True
--
prop-⋀-&& {True} {True} (refl `and` refl) = refl

-- Logical disjunction
prop-||-⋁
  : ∀ {x y : Bool}
  → (x || y) ≡ True
  → (x ≡ True) ⋁ (y ≡ True)
--
prop-||-⋁ {True} {y} refl = inl refl
prop-||-⋁ {False} {True} refl = inr refl

--
prop-⋁-||
  : ∀ {x y : Bool}
  → (x ≡ True) ⋁ (y ≡ True)
  → (x || y) ≡ True
--
prop-⋁-|| {True} (inl refl) = refl
prop-⋁-|| {True} (inr refl) = refl
prop-⋁-|| {False} (inr refl) = refl

-- Logical negation
prop-not-¬
  : ∀ {x : Bool}
  → (not x ≡ True)
  → ¬ (x ≡ True)
--
prop-not-¬ {True} ()

prop-¬-not
  : ∀ {x : Bool}
  → ¬ (x ≡ True)
  → (not x ≡ True)
--
prop-¬-not {False} contra = refl
prop-¬-not {True} contra = case contra refl of λ ()
