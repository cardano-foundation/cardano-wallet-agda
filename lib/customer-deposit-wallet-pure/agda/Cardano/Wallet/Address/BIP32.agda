{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.BIP32 where

open import Haskell.Prelude

open import Haskell.Data.Word.Odd using
  ( Word31
  )

{-----------------------------------------------------------------------------
    BIP32 Paths
------------------------------------------------------------------------------}
data DerivationType : Set where
    Soft     : DerivationType
    Hardened : DerivationType

open DerivationType public

{-# COMPILE AGDA2HS DerivationType #-}

-- | An absolute BIP32 Path.
data BIP32Path : Set where
    Root    : BIP32Path
    Segment : BIP32Path → DerivationType → Word31 → BIP32Path

open BIP32Path public

{-# COMPILE AGDA2HS BIP32Path #-}
