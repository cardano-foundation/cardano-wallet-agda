{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.BIP32_Ed25519 where

open import Haskell.Prelude hiding (fromJust)
open import Haskell.Reasoning

open import Haskell.Data.ByteString using
  ( ByteString
  )
open import Haskell.Data.Word.Odd using
  ( Word31
  )

{-# FOREIGN AGDA2HS
{-# LANGUAGE UnicodeSyntax #-}
import Data.ByteString
  ( ByteString
  )
import Data.Maybe
  ( fromJust
  )
import Data.Word
  ( Word32
  )
import Data.Word.Odd
  ( Word31
  )
import qualified Cardano.Crypto.Wallet as CC
import qualified Data.ByteString as BS
#-}

dummy : Int
dummy = 12 -- needed for Agda2hs to add sufficient imports

{-----------------------------------------------------------------------------
    Extended private and public keys
------------------------------------------------------------------------------}

-- TODO: Extend to encrypted keys
postulate
  XPub : Set  -- plaintext public key
  XPrv : Set  -- plaintext private key

  toXPub : XPrv → XPub

  XSignature : Set
  sign   : XPrv → ByteString → XSignature
  verify : XPub → ByteString → XSignature → Bool

  prop-verify-sign
    : ∀ (xprv : XPrv)
        (msg  : ByteString)
    → let xpub = toXPub xprv
      in  verify xpub msg (sign xprv msg) ≡ True

{-# FOREIGN AGDA2HS
  -- FIXME: We define type synonyms here so that
  -- they can be exported. Ideally, we would re-export from
  -- the Cardano.Wallet.Crypto module.

  -- | Extended public key,
  -- based on the elliptic curve cryptography
  -- [Ed25519](https://en.wikipedia.org/wiki/EdDSA#Ed25519).
  --
  -- Extended keys can be used to create child keys in line
  -- with the [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf)
  -- standard.
  type XPub = CC.XPub

  -- | Extended private key.
  -- based on the elliptic curve cryptography Ed25519.
  -- [Ed25519](https://en.wikipedia.org/wiki/EdDSA#Ed25519).
  --
  -- Extended keys can be used to create child keys in line
  -- with the [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf)
  -- standard.
  type XPrv = CC.XPrv

  -- | Signature created with an 'XPrv', and verifiable with 'XPub'.
  type XSignature = CC.XSignature

  -- | Obtain the public key correspond to a private key.
  toXPub :: XPrv → XPub
  toXPub = CC.toXPub

  -- | Sign a sequence of bytes with a private key.
  sign :: XPrv → ByteString → XSignature
  sign = CC.sign BS.empty

  -- | Verify the signature for a sequence of bytes using the public key.
  verify :: XPub → ByteString → XSignature → Bool
  verify = CC.verify
#-}

postulate
  rawSerialiseXPub : XPub → ByteString
  rawSerialiseXPrv : XPrv → ByteString
  rawSerialiseXSignature : XSignature → ByteString

  prop-rawSerialiseXPub-injective
    : ∀ (x y : XPub)
    → rawSerialiseXPub x ≡ rawSerialiseXPub y
    → x ≡ y

{-# FOREIGN AGDA2HS
  -- | Serialize an 'XPub' to a sequence of bytes.
  rawSerialiseXPub :: XPub → ByteString
  rawSerialiseXPub = CC.unXPub

  -- | Serialize an 'XPrv' to a sequence of bytes.
  rawSerialiseXPrv :: XPrv → ByteString
  rawSerialiseXPrv = CC.unXPrv

  -- | Serialize an 'XSignature' to a sequence of bytes.
  rawSerialiseXSignature :: XSignature → ByteString
  rawSerialiseXSignature = CC.unXSignature
#-}

{-----------------------------------------------------------------------------
    Key derivation
------------------------------------------------------------------------------}

postulate
  deriveXPubSoft : XPub → Word31 → XPub
  deriveXPrvSoft : XPrv → Word31 → XPrv
  deriveXPrvHard : XPrv → Word31 → XPrv

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

{-# FOREIGN AGDA2HS
  -- | Embed a smaller Word into a larger Word.
  word32fromWord31 :: Word31 → Word32
  word32fromWord31 = fromInteger . toInteger

  -- | Derive a child extended public key according to the
  -- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
  deriveXPubSoft :: XPub → Word31 → XPub
  deriveXPubSoft xpub ix =
    fromJust 
      (CC.deriveXPub
        CC.DerivationScheme2
        xpub
        (word32fromWord31 ix)
      )
    -- deriveXPub always returns Just on Word31

  -- | Derive a child extended private key according to the
  -- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
  deriveXPrvSoft :: XPrv → Word31 → XPrv
  deriveXPrvSoft xprv ix = 
    CC.deriveXPrv
      CC.DerivationScheme2
      BS.empty
      xprv
      (word32fromWord31 ix)

  -- | Derive a hardened child extended private key according to the
  -- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
  deriveXPrvHard :: XPrv → Word31 → XPrv
  deriveXPrvHard xprv ix =
    CC.deriveXPrv
      CC.DerivationScheme2
      BS.empty
      xprv
      (0x80000000 + word32fromWord31 ix)
#-}
