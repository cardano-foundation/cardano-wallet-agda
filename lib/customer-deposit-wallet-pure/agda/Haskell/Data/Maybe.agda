{-# OPTIONS --erasure #-}

module Haskell.Data.Maybe where

open import Haskell.Prelude

isNothing : ∀ {a : Set} → Maybe a → Bool
isNothing (Just _) = False
isNothing Nothing = True

isJust : ∀ {a : Set} → Maybe a → Bool
isJust (Just _) = True
isJust Nothing = False

catMaybes : ∀ {a : Set} → List (Maybe a) → List a
catMaybes [] = []
catMaybes (Nothing ∷ xs) = catMaybes xs
catMaybes (Just x ∷ xs) = x ∷ catMaybes xs

fromMaybe : ∀ {a : Set} → a → Maybe a → a
fromMaybe _ (Just a) = a
fromMaybe a Nothing = a

fromJust : (x : Maybe a) → @0 {isJust x ≡ True} → a
fromJust Nothing  = error "fromJust Nothing"
fromJust (Just x) = x

{-# COMPILE AGDA2HS isNothing #-}
{-# COMPILE AGDA2HS isJust #-}
{-# COMPILE AGDA2HS catMaybes #-}
{-# COMPILE AGDA2HS fromMaybe #-}
{-# COMPILE AGDA2HS fromJust #-}

prop-Just-injective
  : ∀ {a : Set} (x y : a)
  → Just x ≡ Just y
  → x ≡ y
prop-Just-injective _ _ refl = refl
