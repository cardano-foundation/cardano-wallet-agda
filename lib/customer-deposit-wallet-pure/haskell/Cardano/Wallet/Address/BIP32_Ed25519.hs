{-# LANGUAGE UnicodeSyntax #-}

module Cardano.Wallet.Address.BIP32_Ed25519 where

import qualified Cardano.Crypto.Wallet as CC
import Data.ByteString
    ( ByteString
    )
import qualified Data.ByteString as BS
import Data.Maybe
    ( fromJust
    )
import Data.Word
    ( Word32
    )
import Data.Word.Odd
    ( Word31
    )

-- * Types

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
toXPub :: XPrv -> XPub
toXPub = CC.toXPub

-- | Sign a sequence of bytes with a private key.
sign :: XPrv -> ByteString -> XSignature
sign = CC.sign BS.empty

-- | Verify the signature for a sequence of bytes using the public key.
verify :: XPub -> ByteString -> XSignature -> Bool
verify = CC.verify

-- * Serialization

-- | Serialize an 'XPub' to a sequence of bytes.
rawSerialiseXPub :: XPub -> ByteString
rawSerialiseXPub = CC.unXPub

-- | Serialize an 'XPrv' to a sequence of bytes.
rawSerialiseXPrv :: XPrv -> ByteString
rawSerialiseXPrv = CC.unXPrv

-- | Serialize an 'XSignature' to a sequence of bytes.
rawSerialiseXSignature :: XSignature -> ByteString
rawSerialiseXSignature = CC.unXSignature

-- * Key derivation

-- | Embed a smaller Word into a larger Word.
word32fromWord31 :: Word31 -> Word32
word32fromWord31 = fromInteger . toInteger

-- | Derive a child extended public key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPubSoft :: XPub -> Word31 -> XPub
deriveXPubSoft xpub ix =
    fromJust
        ( CC.deriveXPub
            CC.DerivationScheme2
            xpub
            (word32fromWord31 ix)
        )

-- deriveXPub always returns Just on Word31

-- | Derive a child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPrvSoft :: XPrv -> Word31 -> XPrv
deriveXPrvSoft xprv ix =
    CC.deriveXPrv
        CC.DerivationScheme2
        BS.empty
        xprv
        (word32fromWord31 ix)

-- | Derive a hardened child extended private key according to the
-- [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf) standard.
deriveXPrvHard :: XPrv -> Word31 -> XPrv
deriveXPrvHard xprv ix =
    CC.deriveXPrv
        CC.DerivationScheme2
        BS.empty
        xprv
        (0x80000000 + word32fromWord31 ix)
