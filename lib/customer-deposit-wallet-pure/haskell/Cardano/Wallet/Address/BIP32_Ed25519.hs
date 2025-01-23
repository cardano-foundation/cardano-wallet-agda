module Cardano.Wallet.Address.BIP32_Ed25519
    ( -- * Types
      XPub
    , XPrv
    , XSignature
    , toXPub
    , sign
    , verify

      -- * Serialization
    , rawSerialiseXPub
    , rawPublicKeyFromXPub
    , rawSerialiseXPrv
    , rawSerialiseXSignature

      -- * Key derivation
    , deriveXPubSoft
    , deriveXPrvSoft
    , deriveXPrvHard
    , deriveXPrvBIP32Path
    )
where

import Cardano.Wallet.Address.BIP32
    ( BIP32Path (Root, Segment)
    , DerivationType (Hardened, Soft)
    )
import Data.Word.Odd (Word31)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.

import qualified Cardano.Crypto.Wallet.Extra as CC
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Maybe (fromJust)

-- |
-- Extended public key,
-- based on the elliptic curve cryptography
-- [Ed25519](https://en.wikipedia.org/wiki/EdDSA#Ed25519).
--
-- Extended keys can be used to create child keys in line
-- with the [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf)
-- standard.
type XPub = CC.XPub

-- |
-- Extended private key,
-- based on the elliptic curve cryptography Ed25519.
-- [Ed25519](https://en.wikipedia.org/wiki/EdDSA#Ed25519).
--
-- Extended keys can be used to create child keys in line
-- with the [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf)
-- standard.
type XPrv = CC.XPrv

-- |
-- Obtain the extended public key corresponding to an extended private key.
toXPub :: XPrv -> XPub
toXPub = CC.toXPub

-- |
-- Signature created with an 'XPrv', and verifiable with 'XPub'.
type XSignature = CC.XSignature

-- |
-- Sign a sequence of bytes with a private key.
sign :: XPrv -> ByteString -> XSignature
sign = CC.sign BS.empty

-- |
-- Verify the signature for a sequence of bytes using the public key.
verify :: XPub -> ByteString -> XSignature -> Bool
verify = CC.verify

-- |
-- Serialize an 'XPub' to a sequence of bytes.
rawSerialiseXPub :: XPub -> ByteString
rawSerialiseXPub = CC.unXPub

-- |
-- Serialize an 'XPrv' to a sequence of bytes.
rawSerialiseXPrv :: XPrv -> ByteString
rawSerialiseXPrv = CC.unXPrv

-- |
-- Serialize an 'XSignature' to a sequence of bytes.
rawSerialiseXSignature :: XSignature -> ByteString
rawSerialiseXSignature = CC.unXSignature

-- |
-- Extract and serialize the public key of an extended public key.
rawPublicKeyFromXPub :: XPub -> ByteString
rawPublicKeyFromXPub = CC.xpubPublicKey

-- |
-- Derive a child extended public key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPubSoft :: XPub -> Word31 -> XPub
deriveXPubSoft xpub ix =
    fromJust
        ( CC.deriveXPub
            CC.DerivationScheme2
            xpub
            (CC.word32fromWord31Low ix)
        )

-- |
-- Derive a child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPrvSoft :: XPrv -> Word31 -> XPrv
deriveXPrvSoft xprv ix =
    CC.deriveXPrv
        CC.DerivationScheme2
        BS.empty
        xprv
        (CC.word32fromWord31Low ix)

-- |
-- Derive a hardened child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPrvHard :: XPrv -> Word31 -> XPrv
deriveXPrvHard xprv ix =
    CC.deriveXPrv
        CC.DerivationScheme2
        BS.empty
        xprv
        (CC.word32fromWord31High ix)

-- |
-- Derive an extended private key from a root private key
-- along a path as described in the
-- [BIP-32](https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki#user-content-The_key_tree) standard.
deriveXPrvBIP32Path :: XPrv -> BIP32Path -> XPrv
deriveXPrvBIP32Path xprv Root = xprv
deriveXPrvBIP32Path xprv (Segment path Hardened ix) =
    deriveXPrvHard (deriveXPrvBIP32Path xprv path) ix
deriveXPrvBIP32Path xprv (Segment path Soft ix) =
    deriveXPrvSoft (deriveXPrvBIP32Path xprv path) ix
