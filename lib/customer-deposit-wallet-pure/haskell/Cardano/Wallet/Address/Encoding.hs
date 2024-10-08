module Cardano.Wallet.Address.Encoding where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, rawSerialiseXPub)
import Cardano.Wallet.Address.Hash (blake2b'224)
import Cardano.Wallet.Read.Address (CompactAddr, fromShortByteString)
import Cardano.Wallet.Read.Chain (NetworkId (Mainnet, Testnet))
import Data.Word (Word8)
import Haskell.Data.ByteString.Short (ShortByteString, singleton, toShort)
import Haskell.Data.Maybe (fromJust)

type KeyHash = ShortByteString

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
data EnterpriseAddr = EnterpriseAddrC
    { net :: NetworkTag
    , pay :: Credential
    }

keyHashFromXPub :: XPub -> KeyHash
keyHashFromXPub xpub =
    toShort (blake2b'224 (rawSerialiseXPub xpub))

-- |
-- Hash public key to obtain a payment or stake credential.
credentialFromXPub :: XPub -> Credential
credentialFromXPub xpub =
    KeyHashObj (toShort (blake2b'224 (rawSerialiseXPub xpub)))

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
-- Compact from of an 'EnterpriseAddr'.
compactAddrFromEnterpriseAddr :: EnterpriseAddr -> CompactAddr
compactAddrFromEnterpriseAddr addr =
    fromJust (fromShortByteString (bytesFromEnterpriseAddr addr))

-- * Properties

-- $prop-compactAddrFromEnterpriseAddr-injective
-- #prop-compactAddrFromEnterpriseAddr-injective#
--
-- [prop-compactAddrFromEnterpriseAddr-injective]:
--
--     Two 'EnterpriseAddr' with the same serialized 'CompactAddr' are equal
--     — assuming that inverting a cryptographic hash is difficult.
--
--     @
--     @0 prop-compactAddrFromEnterpriseAddr-injective
--       : ∀ (x y : EnterpriseAddr)
--       → compactAddrFromEnterpriseAddr x ≡ compactAddrFromEnterpriseAddr y
--       → x ≡ y
--     @

-- $prop-credentialFromXPub-injective
-- #prop-credentialFromXPub-injective#
--
-- [prop-credentialFromXPub-injective]:
--
--     Two 'XPub' that yield the same credential are equal
--     — assuming that inverting a cryptographic hash is difficult.
--
--     @
--     prop-credentialFromXPub-injective
--       : ∀ (x y : XPub)
--       → credentialFromXPub x ≡ credentialFromXPub y
--       → x ≡ y
--     @
