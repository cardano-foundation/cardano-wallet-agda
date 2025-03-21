{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData #-}

module Cardano.Wallet.Deposit.Pure.Address
    ( -- * Deriving addresses
      Customer
    , deriveCustomerAddress

      -- * AddressState

      -- ** Construction
    , AddressState
    , getNetworkTag
    , getXPub
    , emptyFromXPub
    , fromXPubAndCount

      -- ** Address observation
    , isCustomerAddress
      -- $prop-isCustomerAddress-deriveCustomerAddress
    , isChangeAddress
    , isOurs
      -- $prop-isOurs
      -- $prop-isOurs-from-isCustomerAddress
    , getBIP32Path
    , listCustomers
    , knownCustomerAddress
    , getKnownCustomerCount

      -- ** Address creation
    , newChangeAddress
      -- $prop-changeAddress-not-Customer
    , mockMaxLengthChangeAddress
      -- $prop-isOurs-mockMaxLengthChangeAddress-False
    )
where

import Cardano.Wallet.Address.BIP32 (BIP32Path)
import Cardano.Wallet.Address.BIP32_Ed25519 (XPub)
import Cardano.Wallet.Address.Encoding (NetworkTag, fromNetworkId)
import Cardano.Wallet.Deposit.Pure.Address.Customer
    ( Customer
    , DerivationPath (DerivationChange, DerivationCustomer)
    , deriveAddress
    , deriveCustomerAddress
    , deriveMockMaxLengthChangeAddress
    , toBIP32Path
    )
import Cardano.Wallet.Deposit.Read.Temp (Address)
import Cardano.Wallet.Read.Address ()
import Cardano.Wallet.Read.Chain (NetworkId)
import Cardano.Write.Tx.Balance (ChangeAddressGen)
import qualified Data.Map as Map (Map, empty, insert, lookup, toAscList)
import Data.Maybe (isJust)
import Data.Word.Odd (Word31)
import Prelude hiding (null, subtract)

-- |
-- Data type that keeps track of addresses
-- that belong to the Deposit Wallet.
--
-- NOTE: The fields are mean to be read-only,
-- they are exported for technical reasons.
data AddressState = AddressStateC
    { networkId :: NetworkId
    , stateXPub :: XPub
    , addresses :: Map.Map Address Customer
    , customerCount :: Word31
    , change :: Address
    }

deriving instance Show AddressState

-- |
-- Network for which this 'AddressState' tracks addresses.
getNetworkTag :: AddressState -> NetworkTag
getNetworkTag s = fromNetworkId (networkId s)

-- |
-- Public key of the wallet.
getXPub :: AddressState -> XPub
getXPub = \r -> stateXPub r

-- |
-- Efficient test whether an 'Address' belongs to a known 'Customer'.
isCustomerAddress :: AddressState -> Address -> Bool
isCustomerAddress s =
    \addr -> isJust $ Map.lookup addr (addresses s)

-- |
-- Efficient test whether an 'Address' is an internal change address.
isChangeAddress :: AddressState -> Address -> Bool
isChangeAddress = \s -> (change s ==)

-- |
-- Test whether an 'Address' belongs to the wallet.
-- This can be an address of a 'Customer', or an internal change address.
isOurs :: AddressState -> Address -> Bool
isOurs =
    \s addr -> isChangeAddress s addr || isCustomerAddress s addr

-- |
-- Lookup a derivation path from a change address and a map of addresses.
lookupDerivationPathFun
    :: Address
    -> Map.Map Address Customer
    -> Address
    -> Maybe DerivationPath
lookupDerivationPathFun change' addresses' addr =
    if change' == addr
        then Just DerivationChange
        else DerivationCustomer <$> Map.lookup addr addresses'

-- |
-- Test whether an 'Address' is known and look up its 'DerivationPath'.
lookupDerivationPath
    :: AddressState -> Address -> Maybe DerivationPath
lookupDerivationPath s addr =
    lookupDerivationPathFun (change s) (addresses s) addr

-- |
-- Retrieve the full 'BIP32Path' of a known 'Address'.
--
-- Returns 'Nothing' if the address is not from a known 'Customer'
-- or not equal to an internal change address.
getBIP32Path :: AddressState -> Address -> Maybe BIP32Path
getBIP32Path s = fmap toBIP32Path . lookupDerivationPath s

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
-- Test whether an 'Address' is a customer address.
knownCustomerAddress :: Address -> AddressState -> Bool
knownCustomerAddress address =
    elem address . map (\r -> snd r) . listCustomers

-- |
-- Total number of known 'Customer's.
getKnownCustomerCount :: AddressState -> Word31
getKnownCustomerCount = \r -> customerCount r

-- |
-- Create a new associated between 'Customer' and known 'Address'.
createAddress
    :: Customer -> AddressState -> (Address, AddressState)
createAddress c s0 = (addr, s1)
  where
    xpub :: XPub
    xpub = stateXPub s0
    net :: NetworkTag
    net = getNetworkTag s0
    addr :: Address
    addr = deriveCustomerAddress net xpub c
    addresses1 :: Map.Map Address Customer
    addresses1 = Map.insert addr c (addresses s0)
    s1 :: AddressState
    s1 =
        AddressStateC
            (networkId s0)
            (stateXPub s0)
            addresses1
            0
            (change s0)

-- |
-- Create an empty 'AddressState' for a given 'NetworkId' from a public key.
emptyFromXPub :: NetworkId -> XPub -> AddressState
emptyFromXPub net xpub =
    AddressStateC
        net
        xpub
        Map.empty
        0
        (deriveAddress (fromNetworkId net) xpub DerivationChange)

-- |
-- Create an 'AddressState' for a given 'NetworkId' from a public key and
-- a customer count.
fromXPubAndCount :: NetworkId -> XPub -> Word31 -> AddressState
fromXPubAndCount net xpub count =
    AddressStateC
        (networkId s1')
        (stateXPub s1')
        (addresses s1')
        count
        (change s1')
  where
    s0 :: AddressState
    s0 = emptyFromXPub net xpub
    customers :: [Customer]
    customers = if fromEnum count == 0 then [] else [0 .. pred count]
    s1' :: AddressState
    s1' = foldl (\s c -> snd (createAddress c s)) s0 customers

-- |
-- Change address generator employed by 'AddressState'.
newChangeAddress :: AddressState -> ChangeAddressGen ()
newChangeAddress s = \_ -> (change s, ())

-- |
-- Mock address of maximum length
--
-- This address is used by the coin selection algorithm
-- to get the transaction fees right.
-- Addresses created by 'newChangeAddress' are required to be no longer
-- than this address.
-- This address should not be used in a transaction.
mockMaxLengthChangeAddress :: AddressState -> Address
mockMaxLengthChangeAddress s =
    deriveMockMaxLengthChangeAddress (getNetworkTag s) (stateXPub s)

-- * Properties

-- $prop-changeAddress-not-Customer
-- #p:prop-changeAddress-not-Customer#
--
-- [prop-changeAddress-not-Customer]:
--     /Essential property./
--
--     Customer addresses are never change addresses.
--
--     > @0 prop-changeAddress-not-Customer
--     >   : ∀ (s : AddressState)
--     >       (addr : Address)
--     >   → knownCustomerAddress addr s ≡ True
--     >   → ¬(isChange (newChangeAddress s) addr)

-- $prop-isCustomerAddress-deriveCustomerAddress
-- #p:prop-isCustomerAddress-deriveCustomerAddress#
--
-- [prop-isCustomerAddress-deriveCustomerAddress]:
--     If an address is a known customer address,
--     then it was derived from a 'Customer' ID.
--
--     > @0 prop-isCustomerAddress-deriveCustomerAddress
--     >   : ∀ (s : AddressState)
--     >       (addr : Address)
--     >   → isCustomerAddress s addr ≡ True
--     >   → ∃ (λ c → addr ≡ deriveCustomerAddress (getNetworkTag s) (getXPub s) c)

-- $prop-isOurs
-- #p:prop-isOurs#
--
-- [prop-isOurs]:
--     It's ours if it's an internal change address or a known
--     customer address.
--
--     > @0 prop-isOurs
--     >   : ∀ (s : AddressState)
--     >       (addr : Address)
--     >   → isOurs s addr
--     >     ≡ (isChangeAddress s addr || isCustomerAddress s addr)

-- $prop-isOurs-from-isCustomerAddress
-- #p:prop-isOurs-from-isCustomerAddress#
--
-- [prop-isOurs-from-isCustomerAddress]:
--     If known customer address belongs to the wallet.
--
--     > @0 prop-isOurs-from-isCustomerAddress
--     >   : ∀ (s : AddressState)
--     >       (addr : Address)
--     >   → isCustomerAddress s addr ≡ True
--     >   → isOurs s addr ≡ True

-- $prop-isOurs-mockMaxLengthChangeAddress-False
-- #p:prop-isOurs-mockMaxLengthChangeAddress-False#
--
-- [prop-isOurs-mockMaxLengthChangeAddress-False]:
--     'mockMaxLengthChangeAddress' never belongs to the 'AddressState'.
--
--     > @0 prop-isOurs-mockMaxLengthChangeAddress-False
--     >   : ∀ (s : AddressState)
--     >   → isOurs s (mockMaxLengthChangeAddress s) ≡ False
