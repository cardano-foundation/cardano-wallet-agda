{-# OPTIONS --erasure #-}

-- | Monoids with additional properties.
module Data.Monoid.Refinement where

open import Haskell.Prim.Type -- temporary

open import Haskell.Prim
open import Haskell.Prim.Monoid
open import Haskell.Prim.Num
open import Haskell.Prim.Tuple

open import Haskell.Law
open import Haskell.Law.Extensionality
open import Haskell.Law.Num

-------------------------------------------------------------------------------
-- Commutative monoids

record Commutative (a : Type) : Type where
  field
    overlap ⦃ monoid ⦄ : Monoid a

    @0 commutative : ∀ (x y : a) → x <> y ≡ y <> x

open Commutative ⦃...⦄ public

{-# COMPILE AGDA2HS Commutative class #-}

-------------------------------------------------------------------------------
-- Instances

instance
  iCommutativeFun : ⦃ Commutative b ⦄ → Commutative (a → b)
  iCommutativeFun .monoid = iMonoidFun
  iCommutativeFun .commutative f g = ext (λ x → commutative (f x) (g x))

  iCommutativeUnit : Commutative ⊤
  iCommutativeUnit .monoid = iMonoidUnit
  iCommutativeUnit .commutative x y = refl

  iCommutativeTuple₂
    : ⦃ Commutative a ⦄ → ⦃ Commutative b ⦄ → Commutative (a × b)
  iCommutativeTuple₂ .monoid = iMonoidTuple₂
  iCommutativeTuple₂ .commutative (x1 , x2) (y1 , y2)
    rewrite commutative x1 y1
    rewrite commutative x2 y2
    = refl

  iCommutativeTuple₃
    : ⦃ Commutative a ⦄ → ⦃ Commutative b ⦄ → ⦃ Commutative c ⦄
    → Commutative (a × b × c)
  iCommutativeTuple₃ .monoid = iMonoidTuple₃
  iCommutativeTuple₃ .commutative (x1 , x2 , x3) (y1 , y2 , y3)
    rewrite commutative x1 y1
    rewrite commutative x2 y2
    rewrite commutative x3 y3
    = refl

{-# COMPILE AGDA2HS iCommutativeUnit #-}
{-# COMPILE AGDA2HS iCommutativeTuple₂ #-}
{-# COMPILE AGDA2HS iCommutativeTuple₃ #-}

CommutativeSum : ⦃ _ : Num a ⦄ → ⦃ IsLawfulNum a ⦄ → Commutative a
CommutativeSum .monoid = MonoidSum
CommutativeSum .commutative = +-comm

CommutativeConj : Commutative Bool
CommutativeConj .monoid = MonoidConj
CommutativeConj .commutative = prop-&&-sym

CommutativeDisj : Commutative Bool
CommutativeDisj .monoid = MonoidDisj
CommutativeDisj .commutative = prop-||-sym

{- *-comm is not part of IsLawfulNum yet?!

CommutativeProduct : ⦃ _ : Num a ⦄ → ⦃ _ : IsLawfulNum a ⦄ → Commutative a
CommutativeProduct .monoid = MonoidProduct
CommutativeProduct .commutative = *-comm
-}
