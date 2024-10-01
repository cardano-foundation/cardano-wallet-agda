{-# OPTIONS --erasure #-}

module Haskell.Data.Word
    {-
    ; Word8
    ; Word16
    -}
    where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Prim.Integer

open import Agda.Builtin.Word public using (Word64; primWord64FromNat)

{-----------------------------------------------------------------------------
    Enum helpers
------------------------------------------------------------------------------}
private
  fromTo
    : (from : a → Integer) (to : Integer → a)
    → a → a → List a
  fromTo from to a b =
    map to (enumFromTo (from a) (from b))

  fromThenTo
    : (from : a → Integer) (to : Integer → a)
    → (x x₁ : a)
    → @0 ⦃ IsFalse (fromEnum (from x) == fromEnum (from x₁)) ⦄
    → a
    → List a
  fromThenTo from to a a₁ b =
    map to (enumFromThenTo (from a) (from a₁) (from b))

{-----------------------------------------------------------------------------
    Word8
------------------------------------------------------------------------------}
2⁸ : Nat
2⁸ = 256

data Word8 : Set where
    Word8C : Word64 → Word8

instance
  iNumberWord8 : Number Word8
  iNumberWord8 .Number.Constraint n = IsTrue (ltNat n 2⁸)
  iNumberWord8 .fromNat n = Word8C (n2w n)

word8FromNat : Nat → Word8
word8FromNat n = Word8C (primWord64FromNat n)

word8FromInteger : Integer → Word8
word8FromInteger n = Word8C (integerToWord n)

integerFromWord8 : Word8 → Integer
integerFromWord8 (Word8C n) = wordToInteger n

instance
  iEqWord8 : Eq Word8
  iEqWord8 ._==_ (Word8C x) (Word8C y) = eqWord x y

  iOrdFromLessThanWord8 : OrdFromLessThan Word8
  iOrdFromLessThanWord8 .OrdFromLessThan._<_ (Word8C x) (Word8C y) = ltWord x y

  iOrdWord8 : Ord Word8
  iOrdWord8 = record {OrdFromLessThan iOrdFromLessThanWord8}

  iBoundedBelowWord8 : BoundedBelow Word8
  iBoundedBelowWord8 .minBound = 0

  iBoundedAboveWord8 : BoundedAbove Word8
  iBoundedAboveWord8 .maxBound = Word8C (primWord64FromNat (2⁸ - 1))

  iEnumWord8 : Enum Word8
  iEnumWord8 .BoundedBelowEnum      = Just it
  iEnumWord8 .BoundedAboveEnum      = Just it
  iEnumWord8 .fromEnum              = integerToInt ∘ integerFromWord8
  iEnumWord8 .toEnum         n      = word8FromInteger (intToInteger n)
  iEnumWord8 .succ           x      = word8FromInteger (integerFromWord8 x + 1)
  iEnumWord8 .pred           x      = word8FromInteger (integerFromWord8 x - 1)
  iEnumWord8 .enumFromTo     a b    = fromTo integerFromWord8 word8FromInteger a b
  iEnumWord8 .enumFromThenTo a a₁ b = fromThenTo integerFromWord8 word8FromInteger a a₁ b
  iEnumWord8 .enumFrom       a      = fromTo integerFromWord8 word8FromInteger a maxBound
  iEnumWord8 .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo integerFromWord8 word8FromInteger a a₁ maxBound
              else fromThenTo integerFromWord8 word8FromInteger a a₁ minBound


{-----------------------------------------------------------------------------
    Word16
------------------------------------------------------------------------------}
2¹⁶ : Nat
2¹⁶ = 256 * 256

data Word16 : Set where
    Word16C : Word64 → Word16

instance
  iNumberWord16 : Number Word16
  iNumberWord16 .Number.Constraint n = IsTrue (ltNat n 2¹⁶)
  iNumberWord16 .fromNat n = Word16C (n2w n)

word16FromNat : Nat → Word16
word16FromNat n = Word16C (primWord64FromNat n)

word16FromInteger : Integer → Word16
word16FromInteger n = Word16C (integerToWord n)

integerFromWord16 : Word16 → Integer
integerFromWord16 (Word16C n) = wordToInteger n

instance
  iEqWord16 : Eq Word16
  iEqWord16 ._==_ (Word16C x) (Word16C y) = eqWord x y

  iOrdFromLessThanWord16 : OrdFromLessThan Word16
  iOrdFromLessThanWord16 .OrdFromLessThan._<_ (Word16C x) (Word16C y) = ltWord x y

  iOrdWord16 : Ord Word16
  iOrdWord16 = record {OrdFromLessThan iOrdFromLessThanWord16}

  iBoundedBelowWord16 : BoundedBelow Word16
  iBoundedBelowWord16 .minBound = 0

  iBoundedAboveWord16 : BoundedAbove Word16
  iBoundedAboveWord16 .maxBound = Word16C (primWord64FromNat (2⁸ - 1))

  iEnumWord16 : Enum Word16
  iEnumWord16 .BoundedBelowEnum      = Just it
  iEnumWord16 .BoundedAboveEnum      = Just it
  iEnumWord16 .fromEnum              = integerToInt ∘ integerFromWord16
  iEnumWord16 .toEnum         n      = word16FromInteger (intToInteger n)
  iEnumWord16 .succ           x      = word16FromInteger (integerFromWord16 x + 1)
  iEnumWord16 .pred           x      = word16FromInteger (integerFromWord16 x - 1)
  iEnumWord16 .enumFromTo     a b    = fromTo integerFromWord16 word16FromInteger a b
  iEnumWord16 .enumFromThenTo a a₁ b = fromThenTo integerFromWord16 word16FromInteger a a₁ b
  iEnumWord16 .enumFrom       a      = fromTo integerFromWord16 word16FromInteger a maxBound
  iEnumWord16 .enumFromThen   a a₁   =
    if a < a₁ then fromThenTo integerFromWord16 word16FromInteger a a₁ maxBound
              else fromThenTo integerFromWord16 word16FromInteger a a₁ minBound
