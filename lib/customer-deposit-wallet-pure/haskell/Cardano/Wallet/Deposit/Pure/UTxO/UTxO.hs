module Cardano.Wallet.Deposit.Pure.UTxO.UTxO
    ( UTxO
    , null
    , empty
    , dom
    , balance
    , union
      -- $prop-union-empty-left
      -- $prop-union-empty-right
      -- $prop-union-assoc
    , excluding
      -- $prop-excluding-empty
      -- $prop-excluding-dom
      -- $prop-excluding-absorb
      -- $prop-excluding-excluding
      -- $prop-excluding-difference
      -- $prop-excluding-intersection
      -- $prop-excluding-union
    , restrictedBy
    , excludingS
      -- $prop-excluding-excludingS
    , filterByAddress
      -- $prop-filterByAddress-filters
    )
where

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

-- $prop-excluding-absorb
-- #prop-excluding-absorb#
--
-- [prop-excluding-absorb]:
--
--     Taking the union of a 'UTxO' with one of its exclusions
--     does nothing.
--
--     @
--     @0 prop-excluding-absorb
--       : ∀ {x : Set.ℙ TxIn} {utxo : UTxO}
--       → (x ⋪ utxo) ∪ utxo ≡ utxo
--     @

-- $prop-excluding-difference
-- #prop-excluding-difference#
--
-- [prop-excluding-difference]:
--
--     Excluding the difference is the same as excluding
--     everything and putting back the difference.
--
--     @
--     prop-excluding-difference
--       : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--       → (Set.difference x y) ⋪ utxo
--         ≡ (x ⋪ utxo) ∪ (restrictedBy utxo y)
--     @

-- $prop-excluding-dom
-- #prop-excluding-dom#
--
-- [prop-excluding-dom]:
--
--     Excluding the entire domain gives the empty 'UTxO'.
--
--     @
--     prop-excluding-dom
--       : ∀ {utxo : UTxO}
--       → dom utxo ⋪ utxo ≡ empty
--     @

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

-- $prop-excluding-excluding
-- #prop-excluding-excluding#
--
-- [prop-excluding-excluding]:
--
--     Excluding from an exclusion is the same as excluding the union.
--
--     @
--     prop-excluding-excluding
--       : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--       → x ⋪ (y ⋪ utxo) ≡ (Set.union x y) ⋪ utxo
--     @

-- $prop-excluding-excludingS
-- #prop-excluding-excludingS#
--
-- [prop-excluding-excludingS]:
--
--     Not excluding inputs makes no difference if these
--     inputs have nothing in common with the 'UTxO'.
--
--     @
--     prop-excluding-excludingS
--       : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
--       → Set.intersection (dom ua) (dom ub) ≡ Set.empty
--       → (excludingS x ua) ⋪ ub ≡ x ⋪ ub
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

-- $prop-excluding-union
-- #prop-excluding-union#
--
-- [prop-excluding-union]:
--
--     Excluding from a union is the same as excluding
--     from each member of the union.
--
--     @
--     @0 prop-excluding-union
--       : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
--       → x ⋪ (ua ∪ ub) ≡ (x ⋪ ua) ∪ (x ⋪ ub)
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
