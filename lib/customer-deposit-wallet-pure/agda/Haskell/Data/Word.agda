{-# OPTIONS --erasure #-}

module Haskell.Data.Word
    {-
    ; Word8
    -}
    where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Prim.Integer

open import Agda.Builtin.Word public using (Word64; primWord64FromNat)

{-----------------------------------------------------------------------------
    Word
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

  iOrdWord8 : Ord Word8
  iOrdWord8 = ordFromLessThan (λ {(Word8C x) (Word8C y) → ltWord x y})

  iBoundedBelowWord8 : BoundedBelow Word8
  iBoundedBelowWord8 .minBound = 0

  iBoundedAboveWord8 : BoundedAbove Word8
  iBoundedAboveWord8 .maxBound = Word8C (256 - 1)

  iEnumWord8 : Enum Word8
  iEnumWord8 = boundedEnumViaInteger integerFromWord8 word8FromInteger
