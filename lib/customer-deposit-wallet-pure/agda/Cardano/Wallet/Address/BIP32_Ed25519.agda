{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.BIP32_Ed25519
  {-|
  -- * Types
  ; XPub
  ; XPrv
  ; XSignature
    ; toXPub
    ; sign
    ; verify

  -- * Serialization
  ; rawSerialiseXPub
  ; rawSerialiseXPrv
  ; rawSerialiseXSignature

  -- * Key derivation
  ; deriveXPubSoft
  ; deriveXPrvSoft
  ; deriveXPrvHard
  -} where

open import Haskell.Prelude hiding (fromJust)
open import Haskell.Reasoning

open import Haskell.Data.ByteString using
  ( ByteString
  )
open import Haskell.Data.Maybe using
  ( fromJust
  ; isJust
  )
open import Haskell.Data.Word using
  ( Word32
  )
open import Haskell.Data.Word.Odd using
  ( Word31
  )

import Haskell.Cardano.Crypto.Wallet as CC
import Haskell.Data.ByteString as BS

{-----------------------------------------------------------------------------
    Extended private and public keys
------------------------------------------------------------------------------}

-- | Extended public key,
-- based on the elliptic curve cryptography
-- [Ed25519](https://en.wikipedia.org/wiki/EdDSA#Ed25519).
--
-- Extended keys can be used to create child keys in line
-- with the [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf)
-- standard.
XPub : Set
XPub = CC.XPub

-- | Private key, plaintext.
XPrv : Set
XPrv = CC.XPrv

-- | Extended private key.
-- based on the elliptic curve cryptography Ed25519.
-- [Ed25519](https://en.wikipedia.org/wiki/EdDSA#Ed25519).
--
-- Extended keys can be used to create child keys in line
-- with the [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf)
-- standard.
toXPub : XPrv → XPub
toXPub = CC.toXPub

-- | Signature created with an 'XPrv', and verifiable with 'XPub'.
XSignature : Set
XSignature = CC.XSignature

-- | Sign a sequence of bytes with a private key.
sign : XPrv → ByteString → XSignature
sign = CC.sign BS.empty

-- | Verify the signature for a sequence of bytes using the public key.
verify : XPub → ByteString → XSignature → Bool
verify = CC.verify

postulate
  prop-verify-sign
    : ∀ (xprv : XPrv)
        (msg  : ByteString)
    → let xpub = toXPub xprv
      in  verify xpub msg (sign xprv msg) ≡ True

{-# COMPILE AGDA2HS XPub #-}
{-# COMPILE AGDA2HS XPrv #-}
{-# COMPILE AGDA2HS toXPub #-}
{-# COMPILE AGDA2HS XSignature #-}
{-# COMPILE AGDA2HS sign #-}
{-# COMPILE AGDA2HS verify #-}

{-----------------------------------------------------------------------------
    Serialization
------------------------------------------------------------------------------}

-- | Serialize an 'XPub' to a sequence of bytes.
rawSerialiseXPub : XPub → ByteString
rawSerialiseXPub = CC.unXPub

-- | Serialize an 'XPrv' to a sequence of bytes.
rawSerialiseXPrv : XPrv → ByteString
rawSerialiseXPrv = CC.unXPrv

-- | Serialize an 'XSignature' to a sequence of bytes.
rawSerialiseXSignature : XSignature → ByteString
rawSerialiseXSignature = CC.unXSignature

postulate
  prop-rawSerialiseXPub-injective
    : ∀ (x y : XPub)
    → rawSerialiseXPub x ≡ rawSerialiseXPub y
    → x ≡ y

{-# COMPILE AGDA2HS rawSerialiseXPub #-}
{-# COMPILE AGDA2HS rawSerialiseXPrv #-}
{-# COMPILE AGDA2HS rawSerialiseXSignature #-}

{-----------------------------------------------------------------------------
    Key derivation
------------------------------------------------------------------------------}
postulate
  -- 'deriveXPub' always returns 'Just' on 'Word31'
  @0 prop-isJust-deriveXPub
    : ∀ (xpub : XPub) (ix : Word31)
    → isJust
      (CC.deriveXPub CC.DerivationScheme2 xpub (CC.word32fromWord31Low ix))
      ≡ True

-- | Derive a child extended public key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPubSoft : XPub → Word31 → XPub
deriveXPubSoft xpub ix =
  fromJust 
    (CC.deriveXPub
      CC.DerivationScheme2
      xpub
      (CC.word32fromWord31Low ix)
    )
    {prop-isJust-deriveXPub xpub ix}

-- | Derive a child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPrvSoft : XPrv → Word31 → XPrv
deriveXPrvSoft xprv ix = 
  CC.deriveXPrv
    CC.DerivationScheme2
    BS.empty
    xprv
    (CC.word32fromWord31Low ix)

-- | Derive a hardened child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPrvHard : XPrv → Word31 → XPrv
deriveXPrvHard xprv ix =
  CC.deriveXPrv
    CC.DerivationScheme2
    BS.empty
    xprv
    (CC.word32fromWord31High ix)

{-# COMPILE AGDA2HS deriveXPubSoft #-}
{-# COMPILE AGDA2HS deriveXPrvSoft #-}
{-# COMPILE AGDA2HS deriveXPrvHard #-}

postulate
  prop-derive-soft
    : ∀ (xprv : XPrv)
        (ix   : Word31)
    → deriveXPubSoft (toXPub xprv) ix
      ≡ toXPub (deriveXPrvSoft xprv ix)

  -- The following properties about injectivity
  -- are not true in the strict sense,
  -- only cryptographically hard.
  prop-deriveXPubSoft-injective
    : ∀ (xpub1 xpub2 : XPub)
        (ix1   ix2   : Word31)
    → deriveXPubSoft xpub1 ix1 ≡ deriveXPubSoft xpub2 ix2
    → (xpub1 ≡ xpub2 ⋀ ix1 ≡ ix2)

  prop-deriveXPubSoft-not-identity
    : ∀ (xpub : XPub) (ix : Word31)
    → ¬ (deriveXPubSoft xpub ix ≡ xpub)

  prop-deriveXPrvSoft-injective
    : ∀ (xprv    : XPrv)
        (ix1 ix2 : Word31)
    → deriveXPrvSoft xprv ix1 ≡ deriveXPrvSoft xprv ix2
    → ix1 ≡ ix2

  prop-deriveXPrvHard-injective
    : ∀ (xprv    : XPrv)
        (ix1 ix2 : Word31)
    → deriveXPrvHard xprv ix1 ≡ deriveXPrvHard xprv ix2
    → ix1 ≡ ix2
