module Cardano.Wallet.Deposit.Pure.UTxO.UTxO where

import Cardano.Wallet.Deposit.Read (Address)
import Cardano.Wallet.Read.Tx (TxIn, TxOut, getCompactAddr, getValue)
import Cardano.Wallet.Read.Value (Value)
import Data.Set (Set)
import qualified Haskell.Data.Map as Map
    ( Map
    , empty
    , filter
    , keysSet
    , member
    , null
    , restrictKeys
    , unionWith
    , withoutKeys
    )
import qualified Haskell.Data.Set as Set (filter)

-- |
-- The type 'UTxO' is used to keep track of unspent transaction outputs.
-- This type is a mapping from transaction inputs, 'TxIn',
-- which are references, to transaction outputs, 'TxOut',
-- which record the actual currency values, addresses, and other data,
-- that is available for spending.
type UTxO = Map.Map TxIn TxOut

-- |
-- Test whether the 'UTxO' is empty.
null :: UTxO -> Bool
null = Map.null

-- |
-- The empty 'UTxO'.
empty :: UTxO
empty = Map.empty

-- |
-- The domain of a 'UTxO' is the set of /inputs/.
dom :: UTxO -> Set TxIn
dom = Map.keysSet

-- |
-- The total value contained in the outputs.
balance :: UTxO -> Value
balance = foldMap getValue

-- |
-- Left-biased union.
union :: UTxO -> UTxO -> UTxO
union = Map.unionWith (\x y -> x)

-- |
-- Exclude a set of inputs.
excluding :: UTxO -> Set TxIn -> UTxO
excluding = Map.withoutKeys

-- |
-- Restrict to a given set of inputs.
restrictedBy :: UTxO -> Set TxIn -> UTxO
restrictedBy = Map.restrictKeys

-- |
-- Exclude the inputs of a 'UTxO' from a 'Set' of inputs.
excludingS :: Set TxIn -> UTxO -> Set TxIn
excludingS s utxo =
    Set.filter (not . \txin -> Map.member txin utxo) s

-- |
-- Keep those outputs whose address satisfies the predicate.
filterByAddress :: (Address -> Bool) -> UTxO -> UTxO
filterByAddress p = Map.filter (p . getCompactAddr)
