{-# OPTIONS --erasure #-}

module Data.List.Law
    {-|
    -- * List transformations
    ; prop-elem-map

    -- * Searching lists
    -- ** Searching by equality
    ; prop-elem-/=
    ; prop-elem-nub
    ; prop-elem-deleteAll

    -- ** Searching with a predicate
    ; prop-filter-sym
    ; prop-filter-filter

    -- * Special lists
    -- ** \"Set\" operations
      ; prop-nub-empty
      ; prop-nub-::
      ; prop-nub-nub
    ; isDeduplicated
      ; prop-isDeduplicated-empty
      ; prop-isDeduplicated-::
      ; prop-isDeduplicated
      ; prop-isDeduplicated-nub
      ; prop-isDeduplicated-map
    ; deleteAll
      ; prop-deleteAll
      ; prop-deleteAll-==
      ; prop-deleteAll-deleteAll
      ; prop-map-deleteAll

    -- ** Ordered lists
    ; isSorted
    -}
    where

open import Data.Function
open import Haskell.Prelude
open import Haskell.Law.Bool
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Data.List

{-----------------------------------------------------------------------------
    Properties
    List membership
------------------------------------------------------------------------------}
-- | A mapped item is a member of the mapped list
-- iff it is a member of the original list — if the function is injective.
prop-elem-map
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
  → ∀ (f : a → b) → Injective f
  → ∀ (x : a) (ys : List a)
  → elem (f x) (map f ys)
    ≡ elem x ys
--
prop-elem-map f inj x [] = refl
prop-elem-map f inj x (y ∷ ys)
  with f x == f y in eqf
... | True
    rewrite prop-==-Injective f inj x y
    rewrite eqf
    = refl
... | False
    rewrite prop-==-Injective f inj x y
    rewrite eqf
    rewrite prop-elem-map f inj x ys
    = refl

{-----------------------------------------------------------------------------
    Properties
    List membership
------------------------------------------------------------------------------}
-- | Predicate version of list membership.
_∈_ : ∀ {a : Set} ⦃ _ : Eq a ⦄ → a → List a → Set
x ∈ xs = elem x xs ≡ True

-- | An item which is contained in one of the lists
-- but not in the other, witnesses that the lists are unequal.
prop-elem-/=
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x : a) (ys zs : List a)
  → (elem x ys /= elem x zs) ≡ True
  → (ys /= zs) ≡ True
--
prop-elem-/= x [] (z ∷ zs) cond = refl
prop-elem-/= x (y ∷ ys) [] cond = refl
prop-elem-/= x (y ∷ ys) (z ∷ zs) cond
  with y == z in eqyz
... | False
    = refl
prop-elem-/= x (y ∷ ys) (z ∷ zs) cond
    | True
    rewrite equality y z eqyz
    with x == z in eqxz
...   | False = prop-elem-/= x ys zs cond

{-----------------------------------------------------------------------------
    Properties
    Searching with a predicate
------------------------------------------------------------------------------}
-- | Two 'filter' can be applied in any order.
prop-filter-sym
  : ∀ (p q : a → Bool) (xs : List a)
  → filter p (filter q xs)
    ≡ filter q (filter p xs)
--
prop-filter-sym p q [] = refl
prop-filter-sym p q (x ∷ xs)
  with p x in eqp
  with q x in eqq
... | True  | True
    rewrite eqp
    rewrite eqq
    rewrite prop-filter-sym p q xs
    = refl
... | True  | False
    rewrite eqq
    rewrite prop-filter-sym p q xs
    = refl
... | False | True
    rewrite eqp
    = prop-filter-sym p q xs
... | False | False
    = prop-filter-sym p q xs

-- | Filtering with the same predicate twice is the same
-- als filtering once.
prop-filter-filter
  : ∀ (p : a → Bool) (xs : List a)
  → filter p (filter p xs)
    ≡ filter p xs
--
prop-filter-filter p [] = refl
prop-filter-filter p (x ∷ xs)
  with p x in eq
... | True 
    rewrite eq
    rewrite prop-filter-filter p xs
    = refl
... | False
    = prop-filter-filter  p xs

{-----------------------------------------------------------------------------
    Properties
    "Set" operations
------------------------------------------------------------------------------}
-- | Remove /all/ occurrences of the item from the list.
deleteAll : ⦃ Eq a ⦄ → a → List a → List a
deleteAll x = filter (not ∘ (x ==_))

{-# COMPILE AGDA2HS deleteAll #-}

-- | Definition of 'deleteAll'.
prop-deleteAll
  : ∀ ⦃ _ : Eq a ⦄
      (x : a) (xs : List a)
  → deleteAll x xs
    ≡ filter (not ∘ (x ==_)) xs
--
prop-deleteAll x xs = refl

-- | Deleting an item twice is the same as deleting the item once.
--
prop-deleteAll-deleteAll
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x : a) (ys : List a)
  → deleteAll x (deleteAll x ys)
    ≡ deleteAll x ys
--
prop-deleteAll-deleteAll x ys =
  prop-filter-filter (not ∘ (x ==_)) ys

-- | 'deleteAll' commutes with 'nub'.
prop-deleteAll-nub
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x : a) (xs : List a)
  → deleteAll x (nub xs)
    ≡ nub (deleteAll x xs)
--
prop-deleteAll-nub x [] = refl
prop-deleteAll-nub x (y ∷ ys)
  using p ← not ∘ (x ==_)
  using q ← not ∘ (y ==_)
  with x == y in eqxy
... | True
    rewrite sym (equality x y eqxy)
    rewrite prop-filter-filter p (nub ys)
    rewrite prop-deleteAll-nub x ys
    = refl
... | False
    rewrite prop-filter-sym p q (nub ys)
    rewrite prop-deleteAll-nub x ys
    = refl

-- | Recursive definition of 'nub', empty list.
prop-nub-empty
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
  → nub {a} []
    ≡ []
--
prop-nub-empty = refl

-- | Recursive definition of 'nub', non-empty list.
prop-nub-::
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
  → (x : a) (xs : List a)
  → nub (x ∷ xs)
    ≡ x ∷ deleteAll x (nub xs)
--
prop-nub-:: x xs = refl

-- | Applying 'nub' twice is the same as applying it once.
prop-nub-nub
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (xs : List a)
  → nub (nub xs)
    ≡ nub xs
--
prop-nub-nub [] = refl
prop-nub-nub (x ∷ xs)
  using p ← not ∘ (x ==_)
  rewrite sym (prop-deleteAll-nub x (nub xs))
  rewrite prop-filter-filter p (nub (nub xs))
  rewrite prop-nub-nub xs
  = refl

--
lemma-neq-trans
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x y z : a)
  → (x == z) ≡ True
  → (y == z) ≡ False
  → (x == y) ≡ False
--
lemma-neq-trans x y z eqxz
  rewrite equality x z eqxz
  rewrite eqSymmetry y z
  = λ x → x

-- | A deleted item is no longer an element.
--
prop-elem-deleteAll
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x y : a) (zs : List a)
  → elem x (deleteAll y zs)
    ≡ (if x == y then False else elem x zs)
--
prop-elem-deleteAll x y []
  with x == y
... | False = refl
... | True  = refl
prop-elem-deleteAll x y (z ∷ zs)
  with recurse ← prop-elem-deleteAll x y zs
  with y == z in eqyz
... | True
    with x == z in eqxz
...   | True
      rewrite equality' _ _ (trans (equality x z eqxz) (sym (equality y z eqyz)))
      = recurse
...   | False
      = recurse
prop-elem-deleteAll x y (z ∷ zs)
    | False
    with x == z in eqxz
...   | True
      rewrite (lemma-neq-trans x y z eqxz eqyz)
      = refl
...   | False
      = recurse

-- | Deleting an item will do nothing precisely
-- when the item is not an element.
prop-deleteAll-==
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
  → ∀ (x : a) (ys : List a)
  → (deleteAll x ys == ys)
    ≡ not (elem x ys)
--
prop-deleteAll-== x [] = refl
prop-deleteAll-== x (y ∷ ys)
  with x == y in eq
... | True
    with lemma1 ← prop-elem-/= y (deleteAll y ys) (y ∷ ys) 
    rewrite prop-elem-deleteAll y y ys
    rewrite equality x y eq
    rewrite eqReflexivity y
    with lemma2 ← cong not (lemma1 refl)
    rewrite not-not (deleteAll y ys == y ∷ ys)
    rewrite lemma2
    = refl
... | False
    rewrite eqReflexivity y
    = prop-deleteAll-== x ys

-- | An item is an element of the 'nub' iff it is
-- an element of the original list.
--
prop-elem-nub
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (x : a) (ys : List a)
  → elem x (nub ys)
    ≡ elem x ys
--
prop-elem-nub x [] = refl
prop-elem-nub x (y ∷ ys)
  rewrite prop-elem-deleteAll x y (nub ys)
  with x == y
... | True = refl
... | False = prop-elem-nub x ys

-- | Deleting an item and mapping with a function
-- is the same as deleting the mapped item —
-- if the function is injective.
prop-map-deleteAll
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
  → ∀ (f : a → b) → Injective f
  → ∀ (x : a) (ys : List a)
  → map f (deleteAll x ys)
    ≡ deleteAll (f x) (map f ys)
--
prop-map-deleteAll f inj x [] = refl
prop-map-deleteAll f inj x (y ∷ ys)
  with f x == f y in eqf
... | True
    rewrite prop-==-Injective f inj x y
    rewrite eqf
    rewrite prop-map-deleteAll f inj x ys
    = refl
... | False
    rewrite prop-==-Injective f inj x y
    rewrite eqf
    rewrite prop-map-deleteAll f inj x ys
    = refl

{-----------------------------------------------------------------------------
    Properties
    "Set" operations
    isDeduplicated
------------------------------------------------------------------------------}
-- | Decide whether a list does not contain duplicated elements.
isDeduplicated : ∀ ⦃ _ : Eq a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → List a → Bool
isDeduplicated [] = True
isDeduplicated (x ∷ xs) = not (elem x xs) && isDeduplicated xs

{-# COMPILE AGDA2HS isDeduplicated #-}

-- | Recursive definition of 'isDeduplicated', empty list.
prop-isDeduplicated-empty
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
  → isDeduplicated {a} []
    ≡ True
--
prop-isDeduplicated-empty = refl

-- | Recursive definition of 'isDeduplicated', non-empty list.
prop-isDeduplicated-::
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
  → (x : a) (xs : List a)
  → isDeduplicated (x ∷ xs)
    ≡ (not (elem x xs) && isDeduplicated xs)
--
prop-isDeduplicated-:: x xs = refl

-- | A definition of 'isDeduplicated' in terms of 'nub'.
prop-isDeduplicated
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
  → (xs : List a)
  → isDeduplicated xs ≡ (nub xs == xs)
--
prop-isDeduplicated [] = refl
prop-isDeduplicated (x ∷ xs)
  rewrite eqReflexivity x
  with eqDeleteAll ← prop-deleteAll-== x xs
  with elem x xs in eq
... | True
    with lemma1 ← prop-elem-/= x (deleteAll x (nub xs)) xs
    rewrite prop-elem-deleteAll x x (nub xs)
    rewrite eqReflexivity x
    rewrite eq
    = trans (sym (cong not (lemma1 refl))) (not-not _)
... | False
    rewrite prop-deleteAll-nub x xs
    rewrite equality (deleteAll x xs) xs eqDeleteAll
    rewrite prop-isDeduplicated xs
    = refl

-- | The purpose of 'nub' is to deduplicate a list.
prop-isDeduplicated-nub
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      (xs : List a)
  → isDeduplicated (nub xs)
    ≡ True
--
prop-isDeduplicated-nub xs
  rewrite prop-isDeduplicated (nub xs)
  rewrite prop-nub-nub xs
  rewrite eqReflexivity (nub xs)
  = refl

-- | Applying an injective function to a deduplicated list
-- yields a deduplicated list.
prop-isDeduplicated-map
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
      ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
  → ∀ (f : a → b) → Injective f
  → ∀ (xs : List a)
  → isDeduplicated xs ≡ True
  → isDeduplicated (map f xs) ≡ True
--
prop-isDeduplicated-map f inj [] cond = refl
prop-isDeduplicated-map f inj (x ∷ xs) cond
  rewrite eqReflexivity x
  rewrite eqReflexivity (f x)
  using isDedupxs ← &&-rightTrue _ (isDeduplicated xs) cond
  rewrite prop-isDeduplicated-map f inj xs isDedupxs
  using notElemx ← &&-leftTrue (not (elem x xs)) _ cond
  rewrite prop-elem-map f inj x xs
  rewrite notElemx
  = refl

{-----------------------------------------------------------------------------
    Properties
    Sorting
------------------------------------------------------------------------------}
-- | Decide whether a list is sorted.
isSorted : ∀ ⦃ _ : Ord a ⦄ → List a → Bool
isSorted xs = and (zipWith (_<=_) xs (drop 1 xs))

{-# COMPILE AGDA2HS isSorted #-}

postulate
  prop-isSorted-sortOn
    : {{_ : Ord b}}
    → ∀ (xs : List a) (f : a → b)
    → isSorted (map f (sortOn f xs)) ≡ True

  prop-elem-sortOn
    : {{_ : Eq a}} → {{_ : Ord b}}
    → ∀ (x : a) (xs : List a) (f : a → b)
    → elem x (sortOn f xs) ≡ elem x xs
