{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.Encoding
  {-|
  -- * Credentials
  ; KeyHash
    ; keyHashFromXPub
  ; Credential (..)
    ; credentialFromXPub
    ; prop-credentialFromXPub-injective

  -- * Addresses
  -- ** Algebraic types
  ; NetworkTag (..)
    ; fromNetworkId
  ; EnterpriseAddr (..)

  -- ** Binary format
  ; compactAddrFromEnterpriseAddr
    ; prop-compactAddrFromEnterpriseAddr-injective
  -}
  where

open import Haskell.Reasoning
open import Haskell.Prelude hiding (fromJust)

open import Cardano.Wallet.Address.BIP32_Ed25519 using
  ( XPub
  ; rawPublicKeyFromXPub
  ; prop-rawPublicKeyFromXPub-injective
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
    ; prop-singleton-<>-injective
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
-- | Hash of a public key.
KeyHash : Set
KeyHash = ShortByteString

-- | A 'Credential' is the hash of a public key or a script.
-- Credentials represent the owner of the corresponding private keys,
-- or the script.
--
-- (Work in progress: Script hashes are not represented yet.)
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
--
-- An enterprise address consists of a single payment credential
-- which guards who can spend funds at this address.
-- Enterprise addresses do not participate in stake delegation.
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

postulate instance
  iShowCredential : Show Credential
  iShowNetworkTag : Show NetworkTag
  iShowEnterpriseAddr : Show EnterpriseAddr

{-# COMPILE AGDA2HS iShowCredential derive #-}
{-# COMPILE AGDA2HS iShowNetworkTag derive #-}
{-# COMPILE AGDA2HS iShowEnterpriseAddr derive #-}

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
-- | Hash a public key.
keyHashFromXPub : XPub → KeyHash
keyHashFromXPub xpub = toShort (blake2b'224 (rawPublicKeyFromXPub xpub))

-- | Hash a public key to obtain a 'Credential'.
credentialFromXPub : XPub → Credential
credentialFromXPub xpub =
  KeyHashObj (keyHashFromXPub xpub)

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

--
prop-toEnterpriseTag-injective
  : ∀ (x y : NetworkTag)
  → toEnterpriseTag x ≡ toEnterpriseTag y
  → x ≡ y
--
prop-toEnterpriseTag-injective TestnetTag TestnetTag refl = refl
prop-toEnterpriseTag-injective MainnetTag MainnetTag refl = refl

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

-- | Compact / serialized form of an 'EnterpriseAddr'.
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
-- |
-- Two 'XPub' that yield the same credential are equal
-- — assuming that inverting a cryptographic hash is difficult.
prop-credentialFromXPub-injective
  : ∀ (x y : XPub)
  → credentialFromXPub x ≡ credentialFromXPub y
  → x ≡ y
--
prop-credentialFromXPub-injective x y =
  prop-rawPublicKeyFromXPub-injective _ _
  ∘ prop-blake2b'224-injective _ _
  ∘ prop-toShort-injective _ _
  ∘ prop-KeyHashObj-injective _ _

--
prop-bytesFromEnterpriseAddr-injective
  : ∀ (x y : EnterpriseAddr)
  → bytesFromEnterpriseAddr x ≡ bytesFromEnterpriseAddr y
  → x ≡ y
--
prop-bytesFromEnterpriseAddr-injective
  (EnterpriseAddrC netx (KeyHashObj hashx))
  (EnterpriseAddrC nety (KeyHashObj hashy)) eq =
    cong₂ EnterpriseAddrC eqNet (cong KeyHashObj (projr eqPair))
  where
    eqPair =
      prop-singleton-<>-injective (toEnterpriseTag netx) _ hashx hashy eq
    eqNet = prop-toEnterpriseTag-injective _ _ (projl eqPair)

-- |
-- Two 'EnterpriseAddr' with the same serialized 'CompactAddr' are equal
-- — assuming that inverting a cryptographic hash is difficult.
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
