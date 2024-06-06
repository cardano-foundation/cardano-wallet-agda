module Cardano.Wallet.Address.Encoding where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, rawSerialiseXPub)
import Cardano.Wallet.Address.Hash (blake2b'224)
import Cardano.Wallet.Deposit.Read (Addr)
import Data.Word (Word8)
import Haskell.Data.ByteString (singleton)

tagEnterprise :: Word8
tagEnterprise = 97

mkEnterpriseAddress :: XPub -> Addr
mkEnterpriseAddress xpub =
    singleton tagEnterprise <> blake2b'224 (rawSerialiseXPub xpub)
