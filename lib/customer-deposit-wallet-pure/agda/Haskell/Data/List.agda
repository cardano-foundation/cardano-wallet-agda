module Haskell.Data.List where

open import Haskell.Prelude
open import Haskell.Law.Eq

{-----------------------------------------------------------------------------
    Reducing lists (folds)
------------------------------------------------------------------------------}
foldl'
  : ∀ {t : Set → Set} ⦃ _ : Foldable t ⦄
  → (b → a → b) → b → t a → b
foldl' = foldl

{-----------------------------------------------------------------------------
    Searching lists
      Searching with a predicate
------------------------------------------------------------------------------}
partition : (a → Bool) → List a → (List a × List a)
partition p xs = (filter p xs , filter (not ∘ p) xs)

{-----------------------------------------------------------------------------
    Special lists
      "Set operations"
------------------------------------------------------------------------------}
-- | Remove the /first/ occurrence of the item from the list.
delete : ⦃ Eq a ⦄ → a → List a → List a
delete _ [] = []
delete x (y ∷ ys) = if x == y then ys else y ∷ delete x ys

-- | Remove all duplicates.
nub : ⦃ _ : Eq a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → List a → List a
nub [] = []
nub (x ∷ xs) = x ∷ filter (not ∘ (x ==_)) (nub xs)

{-----------------------------------------------------------------------------
    Special lists
      Ordered lists
------------------------------------------------------------------------------}
postulate
  sortOn : ⦃ _ : Ord b ⦄ → (a → b) → List a → List a

sort : ⦃ _ : Ord a ⦄ → List a → List a
sort = sortOn id
