{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.Encoding
    {-
    ; mkEnterpriseAddress
    ; prop-mkEnterpriseAddress-injective
    -}
    where

open import Haskell.Prelude

open import Cardano.Wallet.Address.BIP32_Ed25519 using
  ( XPub
  ; rawSerialiseXPub
  ; prop-rawSerialiseXPub-injective
  )
open import Cardano.Wallet.Address.Hash using
  ( blake2b'224
  ; prop-blake2b'224-injective
  )
open import Cardano.Wallet.Deposit.Read using
  ( CompactAddr
    ; fromShortByteString
    ; prop-fromShortByteString-partially-injective
  )
open import Haskell.Data.ByteString.Short using
  ( ShortByteString
    ; singleton
    ; toShort
    ; prop-toShort-injective
    ; prop-<>-cancel-left
  )
open import Haskell.Data.Maybe using
  ( fromJust
  ; isJust
  ; prop-Just-injective
  ; prop-fromJust-injective
  )
open import Haskell.Data.Word using
  ( Word8
  )

{-----------------------------------------------------------------------------
    Create addresses from public keys

    For magic numbers, see
    https://github.com/cardano-foundation/CIPs/tree/master/CIP-0019
------------------------------------------------------------------------------}

-- | Network tag for enterprise addresses on mainnet.
tagEnterprise : Word8 
tagEnterprise = 0b01100001

{-# COMPILE AGDA2HS tagEnterprise #-}

-- | Create an enterprise address on mainnet in binary format.
--
-- The binary format of addresses is described in
-- [CIP-19](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0019/README.md)
mkEnterpriseAddressBytes : XPub → ShortByteString
mkEnterpriseAddressBytes xpub =
    singleton tagEnterprise <>
      toShort (blake2b'224 (rawSerialiseXPub xpub))

{-# COMPILE AGDA2HS mkEnterpriseAddressBytes #-}

postulate
  prop-mkEnterpriseAddress-isJust
    : ∀ (xpub : XPub)
    → isJust (fromShortByteString (mkEnterpriseAddressBytes xpub)) ≡ True

-- | Create an enterprise address on mainnet from a public key.
-- Knowing the private key allows you to spend outputs with this address.
mkEnterpriseAddress : XPub → CompactAddr
mkEnterpriseAddress xpub =
  fromJust
    (fromShortByteString (mkEnterpriseAddressBytes xpub))
    {prop-mkEnterpriseAddress-isJust xpub}

{-# COMPILE AGDA2HS mkEnterpriseAddress #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}

prop-mkEnterpriseAddressBytes-injective
  : ∀ (x y : XPub)
  → mkEnterpriseAddressBytes x ≡ mkEnterpriseAddressBytes y
  → x ≡ y
prop-mkEnterpriseAddressBytes-injective x y =
  prop-rawSerialiseXPub-injective _ _
    ∘ prop-blake2b'224-injective _ _
    ∘ prop-toShort-injective _ _
    ∘ prop-<>-cancel-left (singleton tagEnterprise) _ _

@0 prop-mkEnterpriseAddress-injective
  : ∀ (x y : XPub)
  → mkEnterpriseAddress x ≡ mkEnterpriseAddress y
  → x ≡ y
prop-mkEnterpriseAddress-injective x y =
  prop-mkEnterpriseAddressBytes-injective _ _
  ∘ prop-fromShortByteString-partially-injective _ _
      (prop-mkEnterpriseAddress-isJust x)
  ∘ prop-fromJust-injective _ _
