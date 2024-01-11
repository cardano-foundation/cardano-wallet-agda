{-# OPTIONS --erasure #-}

module Haskell.Data.ByteString
    {-
    ; ByteString
    -}
    where

open import Haskell.Prelude hiding (lookup; null; map)
open import Haskell.Data.Word using
    ( Word8
    )

{-----------------------------------------------------------------------------
    ByteString
------------------------------------------------------------------------------}

postulate
  ByteString : Set

postulate
  pack   : List Word8 → ByteString
  unpack : ByteString → List Word8

  instance
    iEqByteString  : Eq ByteString
  
  iOrdByteString₀ : Ord ByteString
  
instance
  iOrdByteString : Ord ByteString
  iOrdByteString = record iOrdByteString₀ { super = iEqByteString }

empty : ByteString
empty = pack []

singleton : Word8 → ByteString
singleton x = pack (x ∷ [])

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}

postulate
  prop-pack-∘-unpack
    : ∀ (x : ByteString)
    → pack (unpack x) ≡ x

  prop-unpack-∘-pack
    : ∀ (x : List Word8)
    → unpack (pack x) ≡ x
  
  instance
    iLawfulEqByteString : IsLawfulEq ByteString

prop-pack-injective
  : ∀ (x y : List Word8)
  → pack x ≡ pack y
  → x ≡ y
prop-pack-injective x y eq =
  begin
    x
  ≡⟨ sym (prop-unpack-∘-pack x) ⟩
    unpack (pack x)
  ≡⟨ cong unpack eq ⟩
    unpack (pack y)
  ≡⟨ prop-unpack-∘-pack y ⟩
    y
  ∎

