{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Address.Encoding
    ( -- * Credentials
      KeyHash
    , keyHashFromXPub
    , Credential (..)
    , credentialFromXPub
      -- $prop-credentialFromXPub-injective

      -- * Addresses

      -- ** Algebraic types
    , NetworkTag (..)
    , fromNetworkId
    , EnterpriseAddr (..)

      -- ** Binary format
    , compactAddrFromEnterpriseAddr
      -- $prop-compactAddrFromEnterpriseAddr-injective
    )
where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, rawPublicKeyFromXPub)
import Data.Word (Word8)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.
import Cardano.Crypto.Hash.Monomorphic
    ( blake2b'224
    )
import Cardano.Wallet.Read
    ( CompactAddr
    , NetworkId (..)
    , fromShortByteString
    )
import Data.ByteString.Short
    ( ShortByteString
    , singleton
    , toShort
    )
import Data.Maybe
    ( fromJust
    )

-- |
-- Hash of a public key.
type KeyHash = ShortByteString

-- |
-- A 'Credential' is the hash of a public key or a script.
-- Credentials represent the owner of the corresponding private keys,
-- or the script.
--
-- (Work in progress: Script hashes are not represented yet.)
data Credential = KeyHashObj KeyHash

-- |
-- Tag to distinguish addresses from Cardano test networks and mainnet.
--
-- This tag is used to disallow testnet addresses on mainnet.
-- This is because testnet addresses tend to be generated
-- with little security in mind, and resuing them on mainnet by accident
-- could lead to a loss of funds.
data NetworkTag
    = MainnetTag
    | TestnetTag

-- |
-- Get 'NetworkTag' from 'NetworkId'.
fromNetworkId :: NetworkId -> NetworkTag
fromNetworkId Mainnet = MainnetTag
fromNetworkId (Testnet x) = TestnetTag

-- |
-- Algebraic representation of an enterprise address.
--
-- An enterprise address consists of a single payment credential
-- which guards who can spend funds at this address.
-- Enterprise addresses do not participate in stake delegation.
data EnterpriseAddr = EnterpriseAddrC
    { net :: NetworkTag
    , pay :: Credential
    }

deriving instance Show Credential

deriving instance Show NetworkTag

deriving instance Show EnterpriseAddr

-- |
-- Hash a public key.
keyHashFromXPub :: XPub -> KeyHash
keyHashFromXPub xpub =
    toShort (blake2b'224 (rawPublicKeyFromXPub xpub))

-- |
-- Hash a public key to obtain a 'Credential'.
credentialFromXPub :: XPub -> Credential
credentialFromXPub xpub = KeyHashObj (keyHashFromXPub xpub)

-- |
-- Magic tag for enterprise addresses on testnet and mainnet.
toEnterpriseTag :: NetworkTag -> Word8
toEnterpriseTag TestnetTag = 96
toEnterpriseTag MainnetTag = 97

-- |
-- Canonical binary format of an 'EnterpriseAddr'.
--
-- The binary format of addresses is described in
-- [CIP-19](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0019/README.md)
bytesFromEnterpriseAddr :: EnterpriseAddr -> ShortByteString
bytesFromEnterpriseAddr
    (EnterpriseAddrC network0 (KeyHashObj hash)) =
        singleton (toEnterpriseTag network0) <> hash

-- |
-- Compact / serialized form of an 'EnterpriseAddr'.
compactAddrFromEnterpriseAddr :: EnterpriseAddr -> CompactAddr
compactAddrFromEnterpriseAddr addr =
    fromJust (fromShortByteString (bytesFromEnterpriseAddr addr))

-- * Properties

-- $prop-compactAddrFromEnterpriseAddr-injective
-- #p:prop-compactAddrFromEnterpriseAddr-injective#
--
-- [prop-compactAddrFromEnterpriseAddr-injective]:
--
--     Two 'EnterpriseAddr' with the same serialized 'CompactAddr' are equal
--     — assuming that inverting a cryptographic hash is difficult.
--
--     > @0 prop-compactAddrFromEnterpriseAddr-injective
--     >   : ∀ (x y : EnterpriseAddr)
--     >   → compactAddrFromEnterpriseAddr x ≡ compactAddrFromEnterpriseAddr y
--     >   → x ≡ y

-- $prop-credentialFromXPub-injective
-- #p:prop-credentialFromXPub-injective#
--
-- [prop-credentialFromXPub-injective]:
--
--     Two 'XPub' that yield the same credential are equal
--     — assuming that inverting a cryptographic hash is difficult.
--
--     > prop-credentialFromXPub-injective
--     >   : ∀ (x y : XPub)
--     >   → credentialFromXPub x ≡ credentialFromXPub y
--     >   → x ≡ y
