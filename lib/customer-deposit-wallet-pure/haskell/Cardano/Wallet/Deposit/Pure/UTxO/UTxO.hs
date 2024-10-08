module Cardano.Wallet.Deposit.Pure.UTxO.UTxO where

import Cardano.Wallet.Deposit.Read.Temp (Address)
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
--
-- Infix synonym: @x ⋪ utxo  =  excluding utxo x@.
--
-- Notable properties:
-- [prop-excluding-intersection](#prop-excluding-intersection),
-- [prop-excluding-sym](#prop-excluding-sym)
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

-- * Properties

-- $prop-excluding-empty
-- #prop-excluding-empty#
--
-- [prop-excluding-empty]:
--
--     Excluding the empty set does nothing.
--
--     @
--     @0 prop-excluding-empty
--       : ∀ (utxo : UTxO)
--       → excluding utxo Set.empty ≡ utxo
--     @

-- $prop-excluding-intersection
-- #prop-excluding-intersection#
--
-- [prop-excluding-intersection]:
--
--     Excluding the intersection is the same as the union of the exclusions.
--
--     @
--     @0 prop-excluding-intersection
--       : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--       → (Set.intersection x y) ⋪ utxo ≡ (x ⋪ utxo) ∪ (y ⋪ utxo)
--     @

-- $prop-excluding-sym
-- #prop-excluding-sym#
--
-- [prop-excluding-sym]:
--
--     Excluding two sets of 'TxIn's can be done in either order.
--
--     @
--     prop-excluding-sym
--       : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--       → x ⋪ (y ⋪ utxo) ≡ y ⋪ (x ⋪ utxo)
--     @

-- $prop-filterByAddress-filters
-- #prop-filterByAddress-filters#
--
-- [prop-filterByAddress-filters]:
--
--     Those outputs whose address satisfies the predicate are kept.
--
--     @
--     prop-filterByAddress-filters
--         : ∀ (p : Address → Bool)
--             (utxo : UTxO) (txin : TxIn) (txout : TxOut)
--         → Map.lookup txin utxo ≡ Just txout
--         → Map.member txin (filterByAddress p utxo)
--             ≡ p (getCompactAddr txout)
--     @

-- $prop-union-assoc
-- #prop-union-assoc#
--
-- [prop-union-assoc]:
--
--     'union' is associative.
--
--     @
--     prop-union-assoc
--       : ∀ {ua ub uc : UTxO}
--       → (ua ∪ ub) ∪ uc ≡ ua ∪ (ub ∪ uc)
--     @

-- $prop-union-empty-left
-- #prop-union-empty-left#
--
-- [prop-union-empty-left]:
--
--     'empty' is a left identity of 'union'.
--
--     @
--     prop-union-empty-left
--       : ∀ {utxo : UTxO}
--       → union empty utxo ≡ utxo
--     @

-- $prop-union-empty-right
-- #prop-union-empty-right#
--
-- [prop-union-empty-right]:
--
--     'empty' is a right identity of 'union'.
--
--     @
--     prop-union-empty-right
--       : ∀ {utxo : UTxO}
--       → union utxo empty ≡ utxo
--     @
