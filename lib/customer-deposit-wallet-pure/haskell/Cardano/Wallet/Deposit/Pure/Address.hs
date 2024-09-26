module Cardano.Wallet.Deposit.Pure.Address where

import Cardano.Wallet.Address.BIP32
    ( BIP32Path (Root, Segment)
    , DerivationType (Hardened, Soft)
    )
import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, deriveXPubSoft)
import Cardano.Wallet.Address.Encoding (mkEnterpriseAddress)
import Cardano.Wallet.Deposit.Read (Address)
import qualified Cardano.Wallet.Read.Address (CompactAddr)
import Cardano.Write.Tx.Balance (ChangeAddressGen)
import Data.Word.Odd (Word31)
import qualified Haskell.Data.Map as Map (Map, empty, insert, lookup, toAscList)
import Haskell.Data.Maybe (isJust)

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
    addSuffix path DerivationChange = Segment path Soft 1
    addSuffix path (DerivationCustomer c) =
        Segment (Segment path Soft 0) Soft c

-- |
--
-- (Internal, exported for technical reasons.)
xpubFromDerivationPath :: XPub -> DerivationPath -> XPub
xpubFromDerivationPath xpub DerivationChange =
    deriveXPubSoft xpub 1
xpubFromDerivationPath xpub (DerivationCustomer c) =
    deriveXPubSoft (deriveXPubSoft xpub 0) c

-- |
-- Derive an address from the wallet public key.
--
-- (Internal, exported for technical reasons.)
deriveAddress :: XPub -> DerivationPath -> Address
deriveAddress xpub =
    mkEnterpriseAddress . xpubFromDerivationPath xpub

-- |
-- Derive an address for a customer from the wallet public key.
deriveCustomerAddress :: XPub -> Customer -> Address
deriveCustomerAddress xpub c =
    deriveAddress xpub (DerivationCustomer c)

-- |
-- Data type that keeps track of addresses
-- that belong to the Deposit Wallet.
--
-- NOTE: The fields are mean to be read-only,
-- they are exported for technical reasons.
data AddressState = AddressStateC
    { stateXPub :: XPub
    , addresses :: Map.Map Address Customer
    , change :: Address
    }

-- |
-- Test whether an 'Address' belongs to known 'Customer'.
isCustomerAddress :: AddressState -> Address -> Bool
isCustomerAddress s =
    \addr -> isJust $ Map.lookup addr (addresses s)

-- |
-- (Internal, exported for technical reasons.)
isChangeAddress :: AddressState -> Address -> Bool
isChangeAddress = \s -> (change s ==)

-- |
-- Test whether an 'Address' belongs to the wallet.
isOurs :: AddressState -> Address -> Bool
isOurs =
    \s addr -> isChangeAddress s addr || isCustomerAddress s addr

-- |
--
-- (Internal, exported for technical reasons.)
getDerivationPath'cases
    :: AddressState -> Address -> Maybe Customer -> Maybe DerivationPath
getDerivationPath'cases s addr (Just c) =
    Just (DerivationCustomer c)
getDerivationPath'cases s addr Nothing =
    if isChangeAddress s addr then Just DerivationChange else Nothing

-- |
--
-- (Internal, exported for technical reasons.)
getDerivationPath
    :: AddressState -> Address -> Maybe DerivationPath
getDerivationPath s addr =
    getDerivationPath'cases s addr (Map.lookup addr (addresses s))

-- |
-- Retrieve the full 'BIP32Path' of a known 'Address'.
--
-- Returns 'Nothing' if the address is not known.
getBIP32Path :: AddressState -> Address -> Maybe BIP32Path
getBIP32Path s = fmap toBIP32Path . getDerivationPath s

-- |
-- Helper function
--
-- (Internal, exported for technical reasons.)
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

-- |
-- List all known associations between 'Customer's and their 'Address'es.
listCustomers :: AddressState -> [(Customer, Address)]
listCustomers = map swap . Map.toAscList . \r -> addresses r

-- |
-- Test whether an 'Address' is a change address.
knownCustomerAddress :: Address -> AddressState -> Bool
knownCustomerAddress address =
    elem address . map (\r -> snd r) . listCustomers

-- |
-- Create a new associated between 'Customer' and known 'Address'.
createAddress
    :: Customer -> AddressState -> (Address, AddressState)
createAddress c s0 = (addr, s1)
  where
    xpub :: XPub
    xpub = stateXPub s0
    addr :: Address
    addr = deriveCustomerAddress xpub c
    addresses1
        :: Map.Map Cardano.Wallet.Read.Address.CompactAddr Word31
    addresses1 = Map.insert addr c (addresses s0)
    s1 :: AddressState
    s1 = AddressStateC (stateXPub s0) addresses1 (change s0)

-- |
-- Public key of the wallet.
getXPub :: AddressState -> XPub
getXPub = \r -> stateXPub r

-- |
-- Create an empty 'AddressState' from a public key.
emptyFromXPub :: XPub -> AddressState
emptyFromXPub xpub =
    AddressStateC
        xpub
        Map.empty
        (deriveAddress xpub DerivationChange)

-- |
-- Create an 'AddressState' from a public key and
-- a count of known customers.
fromXPubAndCount :: XPub -> Word31 -> AddressState
fromXPubAndCount xpub knownCustomerCount =
    foldl (\s c -> snd (createAddress c s)) s0 customers
  where
    s0 :: AddressState
    s0 = emptyFromXPub xpub
    customers :: [Word31]
    customers = [0 .. knownCustomerCount]

-- |
-- Change address generator employed by 'AddressState'.
newChangeAddress :: AddressState -> ChangeAddressGen ()
newChangeAddress s = \_ -> (change s, ())
