{-# OPTIONS --erasure #-}

module Haskell.Reasoning.Ord where

open import Haskell.Prelude
open import Haskell.Reasoning.Bool
open import Haskell.Reasoning.Core

{-----------------------------------------------------------------------------
    Properties of min
------------------------------------------------------------------------------}
data Cases-min (x1 x2 : a) {{_ : Ord a}} {{_ : IsLawfulOrd a}} : Set where
    Case-min-x1 : ((x1 <= x2) ≡ True) → (min x1 x2 ≡ x1) → Cases-min x1 x2
    Case-min-x2 : ((x2 <= x1) ≡ True) → (min x1 x2 ≡ x2) → Cases-min x1 x2

--
decide-Cases-min
  : ∀ (x1 x2 : a) {{_ : Ord a}} {{_ : IsLawfulOrd a}}
  → Cases-min x1 x2
--
decide-Cases-min x1 x2 = cases (x1 <= x2) refl
  where
    cases : (b : Bool) → (x1 <= x2) ≡ b → Cases-min x1 x2
    cases True leq = Case-min-x1 leq lem2
      where
        lem2 =
          begin
            min x1 x2
          ≡⟨ equality _ _ (min2if x1 x2) ⟩
            (if (x1 <= x2) then x1 else x2)
          ≡⟨ cong (λ o → if o then x1 else x2) leq ⟩
            x1
          ∎

    cases False leq = Case-min-x2 (trans (lte2gte x2 x1) (gt2gte x1 x2 lem1)) lem2
      where
        lem1 : (x1 > x2) ≡ True
        lem1 =
         begin
            (x1 > x2)
          ≡⟨ sym (not-not (x1 > x2)) ⟩
            not (not (x1 > x2))
          ≡⟨ cong not (sym (lte2ngt x1 x2)) ⟩
            not (x1 <= x2)
          ≡⟨ cong not leq ⟩
            True
          ∎

        lem2 =
          begin
            min x1 x2
          ≡⟨ equality _ _ (min2if x1 x2) ⟩
            (if (x1 <= x2) then x1 else x2)
          ≡⟨ cong (λ o → if o then x1 else x2) leq ⟩
            x2
          ∎

-- min is lesser or equal to the first argument
prop-min-<-x1
  : ∀ (x1 x2 : a) {{_ : Ord a}} {{_ : IsLawfulOrd a}}
  → (min x1 x2 <= x1) ≡ True
--
prop-min-<-x1 x1 x2 = case decide-Cases-min x1 x2 of λ
  { (Case-min-x1 leq eq) →
    begin
      min x1 x2 <= x1
    ≡⟨ cong (λ o → o <= _) eq ⟩
      x1 <= x1
    ≡⟨ reflexivity x1 ⟩
      True
    ∎
  ; (Case-min-x2 leq eq) →
    begin
      min x1 x2 <= x1
    ≡⟨ cong (λ o → o <= _) eq ⟩
      x2 <= x1
    ≡⟨ leq ⟩
      True
    ∎
  }

-- min is lesser or equal to the second argument
prop-min-<-x2
  : ∀ (x1 x2 : a) {{_ : Ord a}} {{_ : IsLawfulOrd a}}
  → (min x1 x2 <= x2) ≡ True
--
prop-min-<-x2 x1 x2 = case decide-Cases-min x1 x2 of λ
  { (Case-min-x1 leq eq) →
    begin
      min x1 x2 <= x2
    ≡⟨ cong (λ o → o <= _) eq ⟩
      x1 <= x2
    ≡⟨ leq ⟩
      True
    ∎
  ; (Case-min-x2 leq eq) →
    begin
      min x1 x2 <= x2
    ≡⟨ cong (λ o → o <= _) eq ⟩
      x2 <= x2
    ≡⟨ reflexivity x2 ⟩
      True
    ∎
  }

--
lemma-<=-expand
  : ∀ (x y z : a) {{_ : Ord a}} {{_ : IsLawfulOrd a}}
  → (y <= z) ≡ True
  → (x <= y) ≡ (x <= y && x <= z)
lemma-<=-expand x y z eq1 = cases (x <= y) refl
  where
    cases : (b : Bool) → (x <= y) ≡ b → (x <= y) ≡ (x <= y && x <= z)
    cases True eq2 =
      begin
        (x <= y)
      ≡⟨ sym (prop-x-&&-True (x <= y)) ⟩
        (x <= y && True)
      ≡⟨ cong (λ o → (x <= y) && o) (sym lem1) ⟩
        (x <= y && x <= z)
      ∎
      where
        lem1 : (x <= z) ≡ True
        lem1 = transitivity x y z (prop-⋀-&& (eq2 `and` eq1))

    cases False eq2 =
      begin
        (x <= y)
      ≡⟨ eq2 ⟩
        False
      ≡⟨⟩
        False && (x <= z)
      ≡⟨ cong (λ o → o && (x <= z)) (sym eq2) ⟩
       (x <= y && x <= z)
      ∎

--
prop-min-universal
  : ∀ (x y1 y2 : a) {{_ : Ord a}} {{_ : IsLawfulOrd a}}
  → (x <= min y1 y2) ≡ (x <= y1 && x <= y2)
--
prop-min-universal x y1 y2 =  case decide-Cases-min y1 y2 of λ
  { (Case-min-x1 leq eq) →
    begin
      x <= min y1 y2
    ≡⟨ cong (λ o → x <= o) eq ⟩
      x <= y1
    ≡⟨ lemma-<=-expand x y1 y2 leq ⟩
      (x <= y1 && x <= y2)
    ∎
  ; (Case-min-x2 leq eq) →
    begin
      x <= min y1 y2
    ≡⟨ cong (λ o → x <= o) eq ⟩
      x <= y2
    ≡⟨ lemma-<=-expand x y2 y1 leq ⟩
      (x <= y2 && x <= y1)
    ≡⟨ &&-sym (x <= y2) (x <= y1) ⟩
      (x <= y1 && x <= y2)
    ∎
  } 

{-----------------------------------------------------------------------------
    Properties of max
------------------------------------------------------------------------------}

--
postulate
 prop-max-universal
  : ∀ (x1 x2 y : a) {{_ : Ord a}} {{_ : IsLawfulOrd a}}
  → (max x1 x2 <= y) ≡ (x1 <= y && x2 <= y)
--

