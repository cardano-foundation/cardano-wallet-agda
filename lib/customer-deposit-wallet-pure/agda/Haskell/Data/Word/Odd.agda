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

  iEnumWord31 : Enum Word31
  iEnumWord31 = boundedEnumViaInteger integerFromWord31 word31FromInteger
