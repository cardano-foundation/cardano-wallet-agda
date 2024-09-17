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

{-----------------------------------------------------------------------------
    Logical connectives and constants
------------------------------------------------------------------------------}
prop-x-&&-True
  : ∀ (x : Bool)
  → (x && True) ≡ x
prop-x-&&-True True = refl
prop-x-&&-True False = refl

prop-x-&&-False
  : ∀ (x : Bool)
  → (x && False) ≡ False
prop-x-&&-False True = refl
prop-x-&&-False False = refl

{-----------------------------------------------------------------------------
    Properties of if_then_else
------------------------------------------------------------------------------}
prop-if-apply
  : ∀ (b : Bool) (t e : a) (f : a → c)
  → f (if b then t else e) ≡ (if b then f t else f e)
prop-if-apply True = λ t e f → refl
prop-if-apply False = λ t e f → refl

prop-if-redundant
  : ∀ (b : Bool) (t : a)
  → (if b then t else t) ≡ t
prop-if-redundant False _ = refl
prop-if-redundant True _ = refl

prop-if-nested
  : ∀ {a : Set} (x y : Bool) (t e : a)
  → (if x then (if y then t else e) else e)
    ≡ (if (x && y) then t else e)
prop-if-nested True  True = λ o e → refl
prop-if-nested True  False = λ o e → refl
prop-if-nested False True = λ o e → refl
prop-if-nested False False = λ o e → refl

@0 prop-if-eq-subst
  : ∀ {{_ : Eq a}} (x y : a) (t : a → b) (e : b)
      (subst : (x == y) ≡ True → t x ≡ t y)
  → (if x == y then t x else e)
    ≡ (if x == y then t y else e)
prop-if-eq-subst x y t e subst =
  case x == y of λ
    { True {{eq}} → cong (λ o → if x == y then o else e) (subst eq)
    ; False {{eq}} →
      begin
        (if x == y then t x else e)
      ≡⟨ cong (λ o → if o then t x else e) eq ⟩
        e
      ≡⟨ sym (cong (λ o → if o then t y else e) eq) ⟩
        (if x == y then t y else e)
      ∎
    }
