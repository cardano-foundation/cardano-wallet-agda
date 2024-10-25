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
    , isOurs
    , getBIP32Path
    , listCustomers
    , knownCustomerAddress
    , getMaxCustomer

      -- ** Address creation
    , createAddress
      -- $prop-create-derive
      -- $prop-create-known
    , newChangeAddress
      -- $prop-changeAddress-not-Customer
    )
where

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
    , fromNetworkId
    )
import Cardano.Wallet.Deposit.Read.Temp (Address)
import qualified Cardano.Wallet.Read.Address (CompactAddr)
import Cardano.Wallet.Read.Chain (NetworkId)
import Cardano.Write.Tx.Balance (ChangeAddressGen)
import Data.Word.Odd (Word31)
import qualified Haskell.Data.Map.Def as Map
    ( Map
    , empty
    , insert
    , lookup
    , toAscList
    )
import Haskell.Data.Maybe (isJust)
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
--
-- (Internal, exported for technical reasons.)
xpubFromDerivationPath :: XPub -> DerivationPath -> XPub
xpubFromDerivationPath xpub DerivationChange =
    deriveXPubSoft (deriveXPubSoft xpub 1) 0
xpubFromDerivationPath xpub (DerivationCustomer c) =
    deriveXPubSoft (deriveXPubSoft xpub 0) c

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
-- Data type that keeps track of addresses
-- that belong to the Deposit Wallet.
--
-- NOTE: The fields are mean to be read-only,
-- they are exported for technical reasons.
data AddressState = AddressStateC
    { networkId :: NetworkId
    , stateXPub :: XPub
    , addresses :: Map.Map Address Customer
    , maxCustomer :: Customer
    , change :: Address
    }

-- |
-- Network for which this 'AddressState' tracks addresses.
getNetworkTag :: AddressState -> NetworkTag
getNetworkTag s = fromNetworkId (networkId s)

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
-- This can be an address of a 'Customer', or an internal change address.
isOurs :: AddressState -> Address -> Bool
isOurs =
    \s addr -> isChangeAddress s addr || isCustomerAddress s addr

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
-- Test whether an 'Address' is a change address.
knownCustomerAddress :: Address -> AddressState -> Bool
knownCustomerAddress address =
    elem address . map (\r -> snd r) . listCustomers

-- |
-- Maximum 'Customer' number that is being tracked.
getMaxCustomer :: AddressState -> Customer
getMaxCustomer = \r -> maxCustomer r

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
    addresses1
        :: Map.Map Cardano.Wallet.Read.Address.CompactAddr Word31
    addresses1 = Map.insert addr c (addresses s0)
    s1 :: AddressState
    s1 =
        AddressStateC
            (networkId s0)
            (stateXPub s0)
            addresses1
            (max c (maxCustomer s0))
            (change s0)

-- |
-- Public key of the wallet.
getXPub :: AddressState -> XPub
getXPub = \r -> stateXPub r

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
-- a count of known customers.
fromXPubAndCount :: NetworkId -> XPub -> Word31 -> AddressState
fromXPubAndCount net xpub knownCustomerCount =
    foldl (\s c -> snd (createAddress c s)) s0 customers
  where
    s0 :: AddressState
    s0 = emptyFromXPub net xpub
    customers :: [Word31]
    customers = [0 .. knownCustomerCount]

-- |
-- Change address generator employed by 'AddressState'.
newChangeAddress :: AddressState -> ChangeAddressGen ()
newChangeAddress s = \_ -> (change s, ())

-- * Properties

-- $prop-changeAddress-not-Customer
-- #prop-changeAddress-not-Customer#
--
-- [prop-changeAddress-not-Customer]:
--     /Essential property./
--
--     Customer addresses are never change addresses.
--
--     @
--     @0 prop-changeAddress-not-Customer
--       : ∀ (s : AddressState)
--           (addr : Address)
--       → knownCustomerAddress addr s ≡ True
--       → ¬(isChange (newChangeAddress s) addr)
--     @

-- $prop-create-derive
-- #prop-create-derive#
--
-- [prop-create-derive]:
--     Creating a customer address is deterministic,
--     and depends essentially on the 'XPub'.
--
--     @
--     prop-create-derive
--       : ∀ (c : Customer)
--           (s0 : AddressState)
--       → let (address , _) = createAddress c s0
--         in  deriveCustomerAddress (getNetworkTag s0) (stateXPub s0) c ≡ address
--     @

-- $prop-create-known
-- #prop-create-known#
--
-- [prop-create-known]:
--     Creating an address makes it known.
--
--     @
--     @0 prop-create-known
--       : ∀ (c  : Customer)
--           (s0 : AddressState)
--       → let (address , s1) = createAddress c s0
--         in  knownCustomerAddress address s1 ≡ True
--     @
