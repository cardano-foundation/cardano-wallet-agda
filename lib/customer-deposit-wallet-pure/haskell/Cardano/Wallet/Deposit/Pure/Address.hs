module Cardano.Wallet.Deposit.Pure.Address where

import Cardano.Wallet.Deposit.Read (Address)
import Cardano.Write.Tx.Balance (ChangeAddressGen)
import Data.Word (Word8)
import Haskell.Crypto.Hash (Digest, HashAlgorithm(hash), TrivialHash, encodeDigest)
import qualified Haskell.Data.ByteString as BS (ByteString, pack)
import qualified Haskell.Data.Map as Map (Map, insert, lookup, toAscList)
import Haskell.Data.Maybe (isJust)

type Customer = Word8

hashFromList :: [Word8] -> BS.ByteString
hashFromList xs = encodeDigest digest
  where
    digest :: Digest TrivialHash
    digest = hash (BS.pack xs)

data DerivationPath = DerivationCustomer Customer
                    | DerivationChange

listFromDerivationPath :: DerivationPath -> [Word8]
listFromDerivationPath DerivationChange = [0]
listFromDerivationPath (DerivationCustomer c) = [1, c]

deriveAddress :: DerivationPath -> Address
deriveAddress = hashFromList . listFromDerivationPath

deriveCustomerAddress :: Customer -> Address
deriveCustomerAddress c = deriveAddress (DerivationCustomer c)

data AddressState = AddressStateC{addresses ::
                                  Map.Map Address Customer,
                                  change :: Address}

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
    addr :: Address
    addr = deriveCustomerAddress c
    addresses1 :: Map.Map BS.ByteString Word8
    addresses1 = Map.insert addr c (addresses s0)
    s1 :: AddressState
    s1 = AddressStateC addresses1 (change s0)

newChangeAddress :: AddressState -> ChangeAddressGen ()
newChangeAddress s = \ _ -> (change s, ())

