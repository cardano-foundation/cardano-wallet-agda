module Haskell.Data.List where

open import Haskell.Prelude

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
