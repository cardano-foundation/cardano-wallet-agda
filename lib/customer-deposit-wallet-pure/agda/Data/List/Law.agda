{-# OPTIONS --erasure #-}

module Data.List.Law where

open import Haskell.Prelude
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
    Sorting
------------------------------------------------------------------------------}
-- | Check whether a list is sorted.
isSorted : ∀ ⦃ _ : Ord a ⦄ → List a → Bool
isSorted xs = and (zipWith (_<=_) xs (drop 1 xs))

postulate
  prop-isSorted-sortOn
    : {{_ : Ord b}}
    → ∀ (xs : List a) (f : a → b)
    → isSorted (map f (sortOn f xs)) ≡ True

  prop-elem-sortOn
    : {{_ : Eq a}} → {{_ : Ord b}}
    → ∀ (x : a) (xs : List a) (f : a → b)
    → elem x (sortOn f xs) ≡ elem x xs
