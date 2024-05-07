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

instance
  iEqDerivationType : Eq DerivationType
  iEqDerivationType ._==_ Soft Soft = True
  iEqDerivationType ._==_ Hardened Hardened = True
  iEqDerivationType ._==_ _ _ = False
{-# COMPILE AGDA2HS iEqDerivationType derive #-}

postulate instance
  iOrdDerivationType : Ord DerivationType
{-# COMPILE AGDA2HS iOrdDerivationType #-}

-- | An absolute BIP32 Path.
data BIP32Path : Set where
    Root    : BIP32Path
    Segment : BIP32Path → DerivationType → Word31 → BIP32Path

open BIP32Path public
{-# COMPILE AGDA2HS BIP32Path #-}

instance
  iEqBIP32Path : Eq BIP32Path
  iEqBIP32Path ._==_ Root Root = True
  iEqBIP32Path ._==_ (Segment a1 b1 c1) (Segment a2 b2 c2) =
    a1 == a2 && b1 == b2 && c1 == c2
  iEqBIP32Path ._==_ _ _ = False
{-# COMPILE AGDA2HS iEqBIP32Path derive #-}

postulate instance
  iOrdBIP32Path : Ord BIP32Path
{-# COMPILE AGDA2HS iOrdBIP32Path #-}
