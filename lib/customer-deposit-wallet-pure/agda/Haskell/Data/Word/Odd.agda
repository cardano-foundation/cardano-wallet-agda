{-# OPTIONS --erasure #-}

module Haskell.Data.Word.Odd
    {-
    ; Word31
    -}
    where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Prim.Integer

open import Agda.Builtin.Word public using (Word64; primWord64FromNat)

{-----------------------------------------------------------------------------
    Word31
------------------------------------------------------------------------------}
2³¹ : Nat
2³¹ = 256 * 256 * 256 * 128

data Word31 : Set where
    Word31C : Word64 → Word31

instance
  iNumberWord31 : Number Word31
  iNumberWord31 .Number.Constraint n = IsTrue (ltNat n 2³¹)
  iNumberWord31 .fromNat n = Word31C (n2w n)

word31FromNat : Nat → Word31
word31FromNat n = Word31C (primWord64FromNat n)

word31FromInteger : Integer → Word31
word31FromInteger n = Word31C (integerToWord n)

integerFromWord31 : Word31 → Integer
integerFromWord31 (Word31C n) = wordToInteger n

instance
  iEqWord31 : Eq Word31
  iEqWord31 ._==_ (Word31C x) (Word31C y) = eqWord x y

  iOrdWord31 : Ord Word31
  iOrdWord31 = ordFromLessThan (λ {(Word31C x) (Word31C y) → ltWord x y})

  iBoundedBelowWord31 : BoundedBelow Word31
  iBoundedBelowWord31 .minBound = 0

  iBoundedAboveWord31 : BoundedAbove Word31
  iBoundedAboveWord31 .maxBound = Word31C (primWord64FromNat (2³¹ - 1))

private
  fromTo
    : (from : a → Integer) (to : Integer → a)
    → a → a → List a
  fromTo from to a b = map to (enumFromTo (from a) (from b))

  fromThenTo
    : (from : a → Integer) (to : Integer → a)
    → (x x₁ : a)
    → @0 ⦃ IsFalse (fromEnum (from x) == fromEnum (from x₁)) ⦄
    → a
    → List a
  fromThenTo from to a a₁ b = map to (enumFromThenTo (from a) (from a₁) (from b))

instance
  iEnumWord31 : Enum Word31
  iEnumWord31 .BoundedBelowEnum      = Just it
  iEnumWord31 .BoundedAboveEnum      = Just it
  iEnumWord31 .fromEnum              = integerToInt ∘ integerFromWord31
  iEnumWord31 .toEnum         n      = word31FromInteger (intToInteger n)
  iEnumWord31 .succ           x      = word31FromInteger (integerFromWord31 x + 1)
  iEnumWord31 .pred           x      = word31FromInteger (integerFromWord31 x - 1)
  iEnumWord31 .enumFromTo     a b    = fromTo integerFromWord31 word31FromInteger a b
  iEnumWord31 .enumFromThenTo a a₁ b = fromThenTo integerFromWord31 word31FromInteger a a₁ b
  iEnumWord31 .enumFrom       a      = fromTo integerFromWord31 word31FromInteger a maxBound
  iEnumWord31 .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo integerFromWord31 word31FromInteger a a₁ maxBound
              else fromThenTo integerFromWord31 word31FromInteger a a₁ minBound
