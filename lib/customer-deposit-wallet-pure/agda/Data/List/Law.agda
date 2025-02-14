{-# OPTIONS --erasure #-}

module Data.List.Law
    {-|
    
    -- * Searching lists
    -- ** Searching by equality
    ; prop-elem-nub
    ; prop-elem-deleteAll

    -- ** Searching with a predicate
    ; prop-filter-filter

    -- * Special lists
    -- ** \"Set\" operations
    ; isDeduplicated
      ; prop-isDeduplicated
    ; deleteAll
      ; prop-deleteAll
      ; prop-deleteAll-deleteAll

    -- ** Ordered lists
    ; isSorted
    -}
    where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Data.List

{-----------------------------------------------------------------------------
    Properties
    List membership
------------------------------------------------------------------------------}
-- | Predicate version of list membership.
_∈_ : ∀ {a : Set} ⦃ _ : Eq a ⦄ → a → List a → Set
x ∈ xs = elem x xs ≡ True

{-----------------------------------------------------------------------------
    Properties
    Searching with a predicate
------------------------------------------------------------------------------}

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
-- | Decide whether a list does not contain duplicated elements.
isDeduplicated : ∀ ⦃ _ : Eq a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → List a → Bool
isDeduplicated xs = nub xs == xs

-- | Definition of 'isDeduplicated'.
prop-isDeduplicated
  : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
  → (xs : List a)
  → isDeduplicated xs ≡ (nub xs == xs)
--
prop-isDeduplicated xs = refl

{-# COMPILE AGDA2HS isDeduplicated #-}

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
