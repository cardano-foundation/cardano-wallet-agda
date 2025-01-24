{-# OPTIONS --erasure #-}

module Data.Maybe.Extra where

open import Haskell.Data.Maybe using (isJust)
open import Haskell.Prelude

fromJust : (x : Maybe a) → @0 {isJust x ≡ True} → a
fromJust Nothing  = error "fromJust Nothing"
fromJust (Just x) = x

{-# COMPILE AGDA2HS fromJust #-}

prop-Just-injective
  : ∀ {a : Set} (x y : a)
  → Just x ≡ Just y
  → x ≡ y
prop-Just-injective _ _ refl = refl

prop-fromJust-injective
  : ∀ {a} (x y : Maybe a)
  → {@0 px : isJust x ≡ True} → {@0 py : isJust y ≡ True}
  → fromJust x {px} ≡ fromJust y {py}
  → x ≡ y
prop-fromJust-injective (Just a) (Just b) refl = refl
