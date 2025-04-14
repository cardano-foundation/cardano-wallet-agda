{-# OPTIONS --erasure #-}

module Data.Bag
  {-|
  ; Bag
  -} where

open import Haskell.Prelude

{-----------------------------------------------------------------------------
    Bag
------------------------------------------------------------------------------}
-- | A unordered, finite collection of items.
-- Items may appear more than once.
--
-- Bag is the free commutative monoid.
record Bag (a : Set) : Set where
  constructor MkBag
  field
    elements : List a

open Bag public

{-# COMPILE AGDA2HS Bag #-}

-- | Delete the first occurrence of an item from the list.
-- Return 'Nothing' if the element does not occur.
delete1 : ⦃ Eq a ⦄ → a → List a → Maybe (List a)
delete1 x [] = Nothing
delete1 x (y ∷ ys) = if x == y then Just ys else fmap (y ∷_) (delete1 x ys)

{-# COMPILE AGDA2HS delete1 #-}

-- | Two lists are equal as bags.
eqBag : ⦃ Eq a ⦄ →  List a → List a → Bool
eqBag []       []       = True
eqBag []       (y ∷ ys) = False
eqBag (x ∷ xs) ys'      = case delete1 x ys' of λ where
    (Just ys) → eqBag xs ys
    Nothing   → False

{-# COMPILE AGDA2HS eqBag #-}

instance
  iEqBag : ⦃ Eq a ⦄ → Eq (Bag a)
  iEqBag ._==_ (MkBag xs) (MkBag ys) = eqBag xs ys

{-# COMPILE AGDA2HS iEqBag derive #-}
