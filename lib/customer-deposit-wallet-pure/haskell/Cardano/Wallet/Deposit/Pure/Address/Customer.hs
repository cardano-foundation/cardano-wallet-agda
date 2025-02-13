module Cardano.Wallet.Deposit.Pure.Address.Customer where

import Cardano.Wallet.Address.BIP32
    ( BIP32Path (Root, Segment)
    , DerivationType (Hardened, Soft)
    )
import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, deriveXPubSoft)
import Cardano.Wallet.Address.Encoding
    ( EnterpriseAddr (EnterpriseAddrC)
    , NetworkTag
    , compactAddrFromEnterpriseAddr
    , credentialFromXPub
    )
import Cardano.Wallet.Deposit.Read.Temp (Address)
import Data.Word.Odd (Word31)
import Prelude hiding (null, subtract)

-- |
-- A 'Customer' is represented as a numerical ID.
--
-- The numerical ID ranges in 'Word31' because that is the range
-- for a step in address derivation, see 'BIP32Path'.
type Customer = Word31

-- |
-- Description of the derivation path used for the Deposit Wallet:
-- Either a 'Customer' or a change address.
data DerivationPath
    = DerivationCustomer Customer
    | DerivationChange

-- |
-- Full 'BIP32Path' corresponding to a 'DerivationPath'.
toBIP32Path :: DerivationPath -> BIP32Path
toBIP32Path = addSuffix prefix
  where
    prefix :: BIP32Path
    prefix =
        Segment
            (Segment (Segment Root Hardened 1857) Hardened 1815)
            Hardened
            0
    addSuffix :: BIP32Path -> DerivationPath -> BIP32Path
    addSuffix path DerivationChange =
        Segment (Segment path Soft 1) Soft 0
    addSuffix path (DerivationCustomer c) =
        Segment (Segment path Soft 0) Soft c

-- |
-- Perform two soft derivation steps.
deriveXPubSoft2 :: XPub -> Word31 -> Word31 -> XPub
deriveXPubSoft2 xpub ix iy =
    deriveXPubSoft (deriveXPubSoft xpub ix) iy

-- |
-- Perform soft derivation from a 'DerivationPath'.
xpubFromDerivationPath :: XPub -> DerivationPath -> XPub
xpubFromDerivationPath xpub DerivationChange =
    deriveXPubSoft2 xpub 1 0
xpubFromDerivationPath xpub (DerivationCustomer c) =
    deriveXPubSoft2 xpub 0 c

-- |
-- Derive an address from the wallet public key.
--
-- (Internal, exported for technical reasons.)
deriveAddress :: NetworkTag -> XPub -> DerivationPath -> Address
deriveAddress net xpub =
    compactAddrFromEnterpriseAddr
        . EnterpriseAddrC net
        . credentialFromXPub
        . xpubFromDerivationPath xpub

-- |
-- Derive an address for a customer from the wallet public key.
deriveCustomerAddress :: NetworkTag -> XPub -> Customer -> Address
deriveCustomerAddress net xpub c =
    deriveAddress net xpub (DerivationCustomer c)

-- |
-- Mock address of maximum length
--
-- This address is used by the coin selection algorithm
-- to get the transaction fees right.
-- Addresses created by 'newChangeAddress' are required to be no longer
-- than this address.
-- This address should not be used in a transaction.
deriveMockMaxLengthChangeAddress :: NetworkTag -> XPub -> Address
deriveMockMaxLengthChangeAddress net xpub =
    compactAddrFromEnterpriseAddr
        . EnterpriseAddrC net
        . credentialFromXPub
        $ deriveXPubSoft2 xpub 17 0
