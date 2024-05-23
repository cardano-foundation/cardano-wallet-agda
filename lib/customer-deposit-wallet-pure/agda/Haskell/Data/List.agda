module Haskell.Data.List where

open import Haskell.Prelude

open import Haskell.Data.List.Prop using
    ( isSorted
    )

{-# FOREIGN AGDA2HS
{-# LANGUAGE UnicodeSyntax #-}
import qualified Data.List
#-}

{-----------------------------------------------------------------------------
    Data.List
------------------------------------------------------------------------------}

foldl'
  : ∀ {t : Set → Set} {{_ : Foldable t}}
    → (b → a → b) → b → t a → b
foldl' = foldl

{-# FOREIGN AGDA2HS
foldl'
  :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl' = Data.List.foldl'
#-}

postulate
  sortOn : {{_ : Ord b}} → (a → b) → List a → List a

  prop-sortOn-isSorted
    : {{_ : Ord b}}
    → ∀ (xs : List a) (f : a → b)
    → isSorted (map f (sortOn f xs)) ≡ True

  prop-sortOn-equal
    : {{_ : Eq a}} → {{_ : Ord b}}
    → ∀ (x : a) (xs : List a) (f : a → b)
    → elem x (sortOn f xs) ≡ elem x xs

{-# FOREIGN AGDA2HS
sortOn :: Ord b => (a → b) → [a] → [a]
sortOn = Data.List.sortOn
#-}
