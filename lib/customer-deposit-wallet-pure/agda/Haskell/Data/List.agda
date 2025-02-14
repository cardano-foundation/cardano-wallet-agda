module Haskell.Data.List where

open import Haskell.Prelude

{-----------------------------------------------------------------------------
    Data.List
------------------------------------------------------------------------------}

foldl'
  : ∀ {t : Set → Set} {{_ : Foldable t}}
    → (b → a → b) → b → t a → b
foldl' = foldl

postulate
  sortOn : {{_ : Ord b}} → (a → b) → List a → List a
