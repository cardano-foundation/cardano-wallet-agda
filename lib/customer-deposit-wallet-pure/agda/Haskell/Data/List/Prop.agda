{-# OPTIONS --erasure #-}

module Haskell.Data.List.Prop where

open import Haskell.Prelude

-- | Predicate version of list membership.
_∈_ : ∀ {a : Set} {{_ : Eq a}} → a → List a → Set
x ∈ xs = elem x xs ≡ True

isSorted : ∀ {{_ : Ord a}} → List a → Bool
isSorted xs = and (zipWith (_<=_) xs (drop 1 xs))
