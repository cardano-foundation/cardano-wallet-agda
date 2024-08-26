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

type Customer = Word31

data DerivationPath
    = DerivationCustomer Customer
    | DerivationChange

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

xpubFromDerivationPath :: XPub -> DerivationPath -> XPub
xpubFromDerivationPath xpub DerivationChange =
    deriveXPubSoft xpub 1
xpubFromDerivationPath xpub (DerivationCustomer c) =
    deriveXPubSoft (deriveXPubSoft xpub 0) c

deriveAddress :: XPub -> DerivationPath -> Address
deriveAddress xpub =
    mkEnterpriseAddress . xpubFromDerivationPath xpub

deriveCustomerAddress :: XPub -> Customer -> Address
deriveCustomerAddress xpub c =
    deriveAddress xpub (DerivationCustomer c)

data AddressState = AddressStateC
    { stateXPub :: XPub
    , addresses :: Map.Map Address Customer
    , change :: Address
    }

isCustomerAddress :: AddressState -> Address -> Bool
isCustomerAddress s =
    \addr -> isJust $ Map.lookup addr (addresses s)

isChangeAddress :: AddressState -> Address -> Bool
isChangeAddress = \s -> (change s ==)

isOurs :: AddressState -> Address -> Bool
isOurs =
    \s addr -> isChangeAddress s addr || isCustomerAddress s addr

getDerivationPath'cases
    :: AddressState -> Address -> Maybe Customer -> Maybe DerivationPath
getDerivationPath'cases s addr (Just c) =
    Just (DerivationCustomer c)
getDerivationPath'cases s addr Nothing =
    if isChangeAddress s addr then Just DerivationChange else Nothing

getDerivationPath
    :: AddressState -> Address -> Maybe DerivationPath
getDerivationPath s addr =
    getDerivationPath'cases s addr (Map.lookup addr (addresses s))

getBIP32Path :: AddressState -> Address -> Maybe BIP32Path
getBIP32Path s = fmap toBIP32Path . getDerivationPath s

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

listCustomers :: AddressState -> [(Customer, Address)]
listCustomers = map swap . Map.toAscList . \r -> addresses r

knownCustomerAddress :: Address -> AddressState -> Bool
knownCustomerAddress address =
    elem address . map (\r -> snd r) . listCustomers

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

getXPub :: AddressState -> XPub
getXPub = \r -> stateXPub r

emptyFromXPub :: XPub -> AddressState
emptyFromXPub xpub =
    AddressStateC
        xpub
        Map.empty
        (deriveAddress xpub DerivationChange)

fromXPubAndCount :: XPub -> Word31 -> AddressState
fromXPubAndCount xpub knownCustomerCount =
    foldl (\s c -> snd (createAddress c s)) s0 customers
  where
    s0 :: AddressState
    s0 = emptyFromXPub xpub
    customers :: [Word31]
    customers = [0 .. knownCustomerCount]

newChangeAddress :: AddressState -> ChangeAddressGen ()
newChangeAddress s = \_ -> (change s, ())
