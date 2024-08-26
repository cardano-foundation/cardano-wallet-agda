module Cardano.Wallet.Address.Encoding where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, rawSerialiseXPub)
import Cardano.Wallet.Address.Hash (blake2b'224)
import Cardano.Wallet.Read.Address (CompactAddr, fromShortByteString)
import Data.Word (Word8)
import Haskell.Data.ByteString.Short (ShortByteString, singleton, toShort)
import Haskell.Data.Maybe (fromJust)

tagEnterprise :: Word8
tagEnterprise = 97

mkEnterpriseAddressBytes :: XPub -> ShortByteString
mkEnterpriseAddressBytes xpub =
    singleton tagEnterprise
        <> toShort (blake2b'224 (rawSerialiseXPub xpub))

mkEnterpriseAddress :: XPub -> CompactAddr
mkEnterpriseAddress xpub =
    fromJust (fromShortByteString (mkEnterpriseAddressBytes xpub))
