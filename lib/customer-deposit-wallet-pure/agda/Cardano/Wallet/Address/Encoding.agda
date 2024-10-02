{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.Encoding where

open import Haskell.Prelude hiding (fromJust)

open import Cardano.Wallet.Address.BIP32_Ed25519 using
  ( XPub
  ; rawSerialiseXPub
  ; prop-rawSerialiseXPub-injective
  )
open import Cardano.Wallet.Address.Hash using
  ( blake2b'224
  ; prop-blake2b'224-injective
  )
open import Cardano.Wallet.Read using
  ( CompactAddr
    ; fromShortByteString
    ; prop-fromShortByteString-partially-injective
  ; NetworkId
    ; Mainnet
    ; Testnet
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
    Algebraic data type for Enterprise addresses
------------------------------------------------------------------------------}
KeyHash : Set
KeyHash = ShortByteString

data Credential : Set where
  KeyHashObj : KeyHash → Credential

-- | Tag to distinguish addresses from Cardano test networks and mainnet.
--
-- This tag is used to disallow testnet addresses on mainnet.
-- This is because testnet addresses tend to be generated
-- with little security in mind, and resuing them on mainnet by accident
-- could lead to a loss of funds.
data NetworkTag : Set where
  MainnetTag : NetworkTag
  TestnetTag : NetworkTag

-- | Get 'NetworkTag' from 'NetworkId'.
fromNetworkId : NetworkId → NetworkTag
fromNetworkId Mainnet = MainnetTag
fromNetworkId (Testnet x) = TestnetTag

-- | Algebraic representation of an enterprise address.
record EnterpriseAddr : Set where
  constructor EnterpriseAddrC
  field
    net : NetworkTag
    pay : Credential

open EnterpriseAddr public

{-# COMPILE AGDA2HS KeyHash #-}
{-# COMPILE AGDA2HS Credential #-}
{-# COMPILE AGDA2HS NetworkTag #-}
{-# COMPILE AGDA2HS fromNetworkId #-}
{-# COMPILE AGDA2HS EnterpriseAddr #-}

--
prop-KeyHashObj-injective
  : ∀ (x y : KeyHash)
  → KeyHashObj x ≡ KeyHashObj y
  → x ≡ y
--
prop-KeyHashObj-injective x y refl = refl

{-----------------------------------------------------------------------------
    XPubs and hashes
------------------------------------------------------------------------------}
keyHashFromXPub : XPub → KeyHash
keyHashFromXPub xpub = toShort (blake2b'224 (rawSerialiseXPub xpub))

-- | Hash public key to obtain a payment or stake credential.
credentialFromXPub : XPub → Credential
credentialFromXPub xpub =
  KeyHashObj (toShort (blake2b'224 (rawSerialiseXPub xpub)))

{-# COMPILE AGDA2HS keyHashFromXPub #-}
{-# COMPILE AGDA2HS credentialFromXPub #-}

{-----------------------------------------------------------------------------
    Binary format of enterprise addresses.

    For magic numbers, see
    https://github.com/cardano-foundation/CIPs/tree/master/CIP-0019
------------------------------------------------------------------------------}

-- | Magic tag for enterprise addresses on testnet and mainnet.
toEnterpriseTag : NetworkTag → Word8
toEnterpriseTag TestnetTag = 0b01100000
toEnterpriseTag MainnetTag = 0b01100001

{-# COMPILE AGDA2HS toEnterpriseTag #-}

-- | Canonical binary format of an 'EnterpriseAddr'.
--
-- The binary format of addresses is described in
-- [CIP-19](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0019/README.md)
--
bytesFromEnterpriseAddr : EnterpriseAddr → ShortByteString
bytesFromEnterpriseAddr (EnterpriseAddrC network0 (KeyHashObj hash)) =
  singleton (toEnterpriseTag network0) <> hash

postulate
  prop-bytesFromEnterpriseAddr-isJust
    : ∀ (addr : EnterpriseAddr)
    → isJust (fromShortByteString (bytesFromEnterpriseAddr addr)) ≡ True

-- | Compact from of an 'EnterpriseAddr'.
compactAddrFromEnterpriseAddr : EnterpriseAddr → CompactAddr
compactAddrFromEnterpriseAddr addr =
  fromJust
    (fromShortByteString (bytesFromEnterpriseAddr addr))
    {prop-bytesFromEnterpriseAddr-isJust addr}

{-# COMPILE AGDA2HS bytesFromEnterpriseAddr #-}
{-# COMPILE AGDA2HS compactAddrFromEnterpriseAddr #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
--
prop-credentialFromXPub-injective
  : ∀ (x y : XPub)
  → credentialFromXPub x ≡ credentialFromXPub y
  → x ≡ y
--
prop-credentialFromXPub-injective x y =
  prop-rawSerialiseXPub-injective _ _
  ∘ prop-blake2b'224-injective _ _
  ∘ prop-toShort-injective _ _
  ∘ prop-KeyHashObj-injective _ _

--
postulate
 prop-bytesFromEnterpriseAddr-injective
  : ∀ (x y : EnterpriseAddr)
  → bytesFromEnterpriseAddr x ≡ bytesFromEnterpriseAddr y
  → x ≡ y

--
@0 prop-compactAddrFromEnterpriseAddr-injective
  : ∀ (x y : EnterpriseAddr)
  → compactAddrFromEnterpriseAddr x ≡ compactAddrFromEnterpriseAddr y
  → x ≡ y
--
prop-compactAddrFromEnterpriseAddr-injective x y =
  prop-bytesFromEnterpriseAddr-injective _ _
  ∘ prop-fromShortByteString-partially-injective _ _
      (prop-bytesFromEnterpriseAddr-isJust x)
  ∘ prop-fromJust-injective _ _
