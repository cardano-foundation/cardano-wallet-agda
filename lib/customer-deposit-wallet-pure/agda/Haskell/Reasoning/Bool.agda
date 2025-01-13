{-# OPTIONS --erasure #-}

module Haskell.Reasoning.Bool where

open import Haskell.Prelude
open import Haskell.Reasoning.Core

{-----------------------------------------------------------------------------
    Properties
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
    Properties
    Logical connectives and constants
------------------------------------------------------------------------------}
--
prop-x-&&-True
  : ∀ (x : Bool)
  → (x && True) ≡ x
--
prop-x-&&-True True = refl
prop-x-&&-True False = refl

--
prop-x-&&-False
  : ∀ (x : Bool)
  → (x && False) ≡ False
--
prop-x-&&-False True = refl
prop-x-&&-False False = refl

--
prop-x-||-True
  : ∀ (x : Bool)
  → (x || True) ≡ True
--
prop-x-||-True True = refl
prop-x-||-True False = refl

--
prop-x-||-False
  : ∀ (x : Bool)
  → (x || False) ≡ x
--
prop-x-||-False True = refl
prop-x-||-False False = refl

{-----------------------------------------------------------------------------
    Properties
    Boolean algebra
    https://en.wikipedia.org/wiki/Boolean_algebra_(structure)
------------------------------------------------------------------------------}
--
prop-||-idem
  : ∀ (a : Bool)
  → (a || a) ≡ a
--
prop-||-idem False = refl
prop-||-idem True = refl

--
prop-||-assoc
  : ∀ (a b c : Bool)
  → ((a || b) || c) ≡ (a || (b || c))
--
prop-||-assoc False b c = refl
prop-||-assoc True b c = refl

--
prop-||-sym
  : ∀ (a b : Bool)
  → (a || b) ≡ (b || a)
--
prop-||-sym False False = refl
prop-||-sym False True = refl
prop-||-sym True False = refl
prop-||-sym True True = refl

--
prop-||-absorb
  : ∀ (a b : Bool)
  → (a || (a && b)) ≡ a
--
prop-||-absorb False b = refl
prop-||-absorb True b = refl

--
prop-||-identity
  : ∀ (a : Bool)
  → (a || False) ≡ a
--
prop-||-identity False = refl
prop-||-identity True = refl

--
prop-||-&&-distribute
  : ∀ (a b c : Bool)
  → (a || (b && c)) ≡ ((a || b) && (a || c))
--
prop-||-&&-distribute False b c = refl
prop-||-&&-distribute True b c = refl

--
prop-||-complement
  : ∀ (a : Bool)
  → (a || not a) ≡ True
--
prop-||-complement False = refl
prop-||-complement True = refl

--
prop-&&-idem
  : ∀ (a : Bool)
  → (a && a) ≡ a
--
prop-&&-idem False = refl
prop-&&-idem True = refl

--
prop-&&-assoc
  : ∀ (a b c : Bool)
  → ((a && b) && c) ≡ (a && (b && c))
--
prop-&&-assoc False b c = refl
prop-&&-assoc True b c = refl

--
prop-&&-sym
  : ∀ (a b : Bool)
  → (a && b) ≡ (b && a)
--
prop-&&-sym False False = refl
prop-&&-sym False True = refl
prop-&&-sym True False = refl
prop-&&-sym True True = refl

--
prop-&&-absorb
  : ∀ (a b : Bool)
  → (a && (a || b)) ≡ a
--
prop-&&-absorb False b = refl
prop-&&-absorb True b = refl

--
prop-&&-identity
  : ∀ (a : Bool)
  → (a && True) ≡ a
--
prop-&&-identity False = refl
prop-&&-identity True = refl

--
prop-&&-||-distribute
  : ∀ (a b c : Bool)
  → (a && (b || c)) ≡ ((a && b) || (a && c))
--
prop-&&-||-distribute False b c = refl
prop-&&-||-distribute True b c = refl

--
prop-&&-complement
  : ∀ (a : Bool)
  → (a && not a) ≡ False
--
prop-&&-complement False = refl
prop-&&-complement True = refl

--
prop-deMorgan-not-&&
  : ∀ (a b : Bool)
  → not (a && b) ≡ (not a || not b)
--
prop-deMorgan-not-&& False b = refl
prop-deMorgan-not-&& True b = refl

--
prop-deMorgan-not-||
  : ∀ (a b : Bool)
  → not (a || b) ≡ (not a && not b)
--
prop-deMorgan-not-|| False b = refl
prop-deMorgan-not-|| True b = refl

{-----------------------------------------------------------------------------
    Properties
    if_then_else
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
