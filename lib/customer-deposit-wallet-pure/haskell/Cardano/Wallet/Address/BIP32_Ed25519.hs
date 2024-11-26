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
    , rawSerialiseXPrv
    , rawSerialiseXSignature

      -- * Key derivation
    , deriveXPubSoft
    , deriveXPrvSoft
    , deriveXPrvHard
    )
where

import Data.Word.Odd (Word31)
import qualified Haskell.Cardano.Crypto.Wallet as CC
    ( DerivationScheme (DerivationScheme2)
    , XPrv
    , XPub
    , XSignature
    , deriveXPrv
    , deriveXPub
    , sign
    , toXPub
    , unXPrv
    , unXPub
    , unXSignature
    , verify
    , word32fromWord31High
    , word32fromWord31Low
    )
import Haskell.Data.ByteString (ByteString)
import qualified Haskell.Data.ByteString as BS (empty)
import Haskell.Data.Maybe (fromJust)
import Prelude hiding (null, subtract)

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
-- Private key, plaintext.
type XPrv = CC.XPrv

-- |
-- Extended private key.
-- based on the elliptic curve cryptography Ed25519.
-- [Ed25519](https://en.wikipedia.org/wiki/EdDSA#Ed25519).
--
-- Extended keys can be used to create child keys in line
-- with the [BIP-32_Ed25519](https://input-output-hk.github.io/adrestia/static/Ed25519_BIP.pdf)
-- standard.
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
