{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.BIP32 where

open import Haskell.Prelude

open import Haskell.Data.Word.Odd using
  ( Word31
  )

{-----------------------------------------------------------------------------
    BIP32 Paths
------------------------------------------------------------------------------}
-- | Method for deriving child keys.
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

postulate instance
  iShowDerivationType : Show DerivationType
{-# COMPILE AGDA2HS iShowDerivationType derive #-}

{-| An absolute path according to the
[BIP-32](https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki) standard.

Example:
The example notated in the standard as

> m/3H/2/5

corresponds to the value

> Segment (Segment (Segment Root Hardened 3) Soft 2) Soft 5
-}
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
{-# COMPILE AGDA2HS iOrdBIP32Path derive #-}

postulate instance
  iShowBIP32Path : Show BIP32Path
{-# COMPILE AGDA2HS iShowBIP32Path derive #-}
