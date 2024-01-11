module Cardano.Wallet.Deposit.Pure.UTxO where

import Cardano.Wallet.Deposit.Read (Address, TxIn, TxOut(address, value), Value)
import Data.Set (Set)
import qualified Haskell.Data.Map as Map (Map, empty, filter, keysSet, member, null, unionWith, withoutKeys)
import qualified Haskell.Data.Set as Set (filter)

type UTxO = Map.Map TxIn TxOut

null :: UTxO -> Bool
null = Map.null

empty :: UTxO
empty = Map.empty

dom :: UTxO -> Set TxIn
dom = Map.keysSet

balance :: UTxO -> Value
balance = foldMap (\ r -> value r)

union :: UTxO -> UTxO -> UTxO
union = Map.unionWith (\ x y -> x)

excluding :: UTxO -> Set TxIn -> UTxO
excluding = Map.withoutKeys

excludingS :: Set TxIn -> UTxO -> Set TxIn
excludingS s utxo
  = Set.filter (not . \ txin -> Map.member txin utxo) s

filterByAddress :: (Address -> Bool) -> UTxO -> UTxO
filterByAddress p = Map.filter (p . \ r -> address r)
