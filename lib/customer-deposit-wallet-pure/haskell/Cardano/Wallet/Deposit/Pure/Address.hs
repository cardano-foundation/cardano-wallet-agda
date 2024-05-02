module Cardano.Wallet.Deposit.Pure.Address where

import Cardano.Wallet.Address.BIP32_Ed25519 (XPub, deriveXPubSoft, rawSerialiseXPub)
import Cardano.Wallet.Address.Hash (blake2b'256)
import Cardano.Wallet.Deposit.Read (Address)
import Cardano.Write.Tx.Balance (ChangeAddressGen)
import Data.Word.Odd (Word31)
import qualified Haskell.Data.ByteString as BS (ByteString)
import qualified Haskell.Data.Map as Map (Map, empty, insert, lookup, toAscList)
import Haskell.Data.Maybe (isJust)

type Customer = Word31

hashFromXPub :: XPub -> BS.ByteString
hashFromXPub = blake2b'256 . rawSerialiseXPub

data DerivationPath = DerivationCustomer Customer
                    | DerivationChange

xpubFromDerivationPath :: XPub -> DerivationPath -> XPub
xpubFromDerivationPath xpub DerivationChange
  = deriveXPubSoft xpub 0
xpubFromDerivationPath xpub (DerivationCustomer c)
  = deriveXPubSoft (deriveXPubSoft xpub 1) c

deriveAddress :: XPub -> DerivationPath -> Address
deriveAddress xpub = hashFromXPub . xpubFromDerivationPath xpub

deriveCustomerAddress :: XPub -> Customer -> Address
deriveCustomerAddress xpub c
  = deriveAddress xpub (DerivationCustomer c)

data AddressState = AddressStateC{stateXPub :: XPub,
                                  addresses :: Map.Map Address Customer, change :: Address}

isCustomerAddress :: AddressState -> Address -> Bool
isCustomerAddress s
  = \ addr -> isJust $ Map.lookup addr (addresses s)

isChangeAddress :: AddressState -> Address -> Bool
isChangeAddress = \ s -> (change s ==)

isOurs :: AddressState -> Address -> Bool
isOurs
  = \ s addr -> isChangeAddress s addr || isCustomerAddress s addr

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

listCustomers :: AddressState -> [(Customer, Address)]
listCustomers = map swap . Map.toAscList . \ r -> addresses r

knownCustomerAddress :: Address -> AddressState -> Bool
knownCustomerAddress address
  = elem address . map (\ r -> snd r) . listCustomers

createAddress ::
              Customer -> AddressState -> (Address, AddressState)
createAddress c s0 = (addr, s1)
  where
    xpub :: XPub
    xpub = stateXPub s0
    addr :: Address
    addr = deriveCustomerAddress xpub c
    addresses1 :: Map.Map BS.ByteString Word31
    addresses1 = Map.insert addr c (addresses s0)
    s1 :: AddressState
    s1 = AddressStateC (stateXPub s0) addresses1 (change s0)

getXPub :: AddressState -> XPub
getXPub = \ r -> stateXPub r

emptyFromXPub :: XPub -> AddressState
emptyFromXPub xpub
  = AddressStateC xpub Map.empty
      (deriveAddress xpub DerivationChange)

fromXPubAndCount :: XPub -> Word31 -> AddressState
fromXPubAndCount xpub knownCustomerCount
  = foldl (\ s c -> snd (createAddress c s)) s0 customers
  where
    s0 :: AddressState
    s0 = emptyFromXPub xpub
    customers :: [Word31]
    customers = [0 .. knownCustomerCount]

newChangeAddress :: AddressState -> ChangeAddressGen ()
newChangeAddress s = \ _ -> (change s, ())

