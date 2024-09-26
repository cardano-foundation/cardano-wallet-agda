module Cardano.Wallet.Address.Encoding where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, rawSerialiseXPub)
import Cardano.Wallet.Address.Hash (blake2b'224)
import Cardano.Wallet.Read.Address (CompactAddr, fromShortByteString)
import Data.Word (Word8)
import Haskell.Data.ByteString.Short (ShortByteString, singleton, toShort)
import Haskell.Data.Maybe (fromJust)

-- |
-- Network tag for enterprise addresses on mainnet.
tagEnterprise :: Word8
tagEnterprise = 97

-- |
-- Create an enterprise address on mainnet in binary format.
--
-- The binary format of addresses is described in
-- [CIP-19](https://github.com/cardano-foundation/CIPs/blob/master/CIP-0019/README.md)
mkEnterpriseAddressBytes :: XPub -> ShortByteString
mkEnterpriseAddressBytes xpub =
    singleton tagEnterprise
        <> toShort (blake2b'224 (rawSerialiseXPub xpub))

-- |
-- Create an enterprise address on mainnet from a public key.
-- Knowing the private key allows you to spend outputs with this address.
mkEnterpriseAddress :: XPub -> CompactAddr
mkEnterpriseAddress xpub =
    fromJust (fromShortByteString (mkEnterpriseAddressBytes xpub))
