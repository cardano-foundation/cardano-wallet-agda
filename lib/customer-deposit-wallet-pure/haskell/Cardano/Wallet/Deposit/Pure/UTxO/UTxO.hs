module Cardano.Wallet.Deposit.Pure.UTxO.UTxO
    ( UTxO
    , null
    , empty
    , dom
    , disjoint
      -- $prop-disjoint-dom
      -- $prop-disjoint-empty
    , balance
    , union
      -- $prop-union-empty-left
      -- $prop-union-empty-right
      -- $prop-union-assoc
      -- $prop-union-sym
    , excluding
      -- $prop-excluding-empty
      -- $prop-excluding-dom
      -- $prop-excluding-absorb
      -- $prop-excluding-excluding
      -- $prop-excluding-sym
      -- $prop-excluding-difference
      -- $prop-excluding-intersection
      -- $prop-excluding-union
    , restrictedBy
      -- $prop-restrictedBy-dom
      -- $prop-restrictedBy-disjoint
      -- $prop-restrictedBy-union
      -- $prop-union-restrictedBy-absorbs
    , excludingS
      -- $prop-excludingS
      -- $prop-excluding-excludingS
    , filterByAddress
      -- $prop-filterByAddress-filters
    )
where

import Cardano.Wallet.Deposit.Read.Temp (Address)
import Cardano.Wallet.Read.Tx (TxIn, TxOut, getCompactAddr, getValue)
import Cardano.Wallet.Read.Value (Value)
import Data.Map ()
import qualified Data.Map as Map
    ( Map
    , disjoint
    , empty
    , filter
    , keysSet
    , member
    , null
    , restrictKeys
    , unionWith
    , withoutKeys
    )
import Data.Set (Set)
import qualified Data.Set as Set (filter)
import Prelude hiding (null, subtract)

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
-- Test whether the domains of the 'UTxO' are disjoint.
disjoint :: UTxO -> UTxO -> Bool
disjoint = Map.disjoint

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
-- [prop-excluding-intersection](#p:prop-excluding-intersection),
-- [prop-excluding-sym](#p:prop-excluding-sym)
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

-- $prop-disjoint-dom
-- #p:prop-disjoint-dom#
--
-- [prop-disjoint-dom]:
--
--     Two 'UTxO' are 'disjoint' if their 'dom'ains are disjoint.
--
--     > prop-disjoint-dom
--     >   : ∀ {ua ub : UTxO}
--     >   → disjoint ua ub ≡ Set.disjoint (dom ua) (dom ub)

-- $prop-disjoint-empty
-- #p:prop-disjoint-empty#
--
-- [prop-disjoint-empty]:
--
--     The 'empty' 'UTxO' is always 'disjoint'.
--
--     > prop-disjoint-empty
--     >   : ∀ {ua : UTxO}
--     >   → disjoint empty ua ≡ True

-- $prop-excluding-absorb
-- #p:prop-excluding-absorb#
--
-- [prop-excluding-absorb]:
--
--     Taking the union of a 'UTxO' with one of its exclusions
--     does nothing.
--
--     > @0 prop-excluding-absorb
--     >   : ∀ {x : Set.ℙ TxIn} {utxo : UTxO}
--     >   → (x ⋪ utxo) ∪ utxo ≡ utxo

-- $prop-excluding-difference
-- #p:prop-excluding-difference#
--
-- [prop-excluding-difference]:
--
--     Excluding the difference is the same as excluding
--     everything and putting back the difference.
--
--     > prop-excluding-difference
--     >   : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--     >   → (Set.difference x y) ⋪ utxo
--     >     ≡ (x ⋪ utxo) ∪ (restrictedBy utxo y)

-- $prop-excluding-dom
-- #p:prop-excluding-dom#
--
-- [prop-excluding-dom]:
--
--     Excluding the entire domain gives the empty 'UTxO'.
--
--     > prop-excluding-dom
--     >   : ∀ {utxo : UTxO}
--     >   → dom utxo ⋪ utxo ≡ empty

-- $prop-excluding-empty
-- #p:prop-excluding-empty#
--
-- [prop-excluding-empty]:
--
--     Excluding the empty set does nothing.
--
--     > @0 prop-excluding-empty
--     >   : ∀ (utxo : UTxO)
--     >   → excluding utxo Set.empty ≡ utxo

-- $prop-excluding-excluding
-- #p:prop-excluding-excluding#
--
-- [prop-excluding-excluding]:
--
--     Excluding from an exclusion is the same as excluding the union.
--
--     > prop-excluding-excluding
--     >   : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--     >   → x ⋪ (y ⋪ utxo) ≡ (Set.union x y) ⋪ utxo

-- $prop-excluding-excludingS
-- #p:prop-excluding-excludingS#
--
-- [prop-excluding-excludingS]:
--
--     Not excluding inputs makes no difference if these
--     inputs have nothing in common with the 'UTxO'.
--
--     > prop-excluding-excludingS
--     >   : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
--     >   → disjoint ua ub ≡ True
--     >   → (excludingS x ua) ⋪ ub ≡ x ⋪ ub

-- $prop-excluding-intersection
-- #p:prop-excluding-intersection#
--
-- [prop-excluding-intersection]:
--
--     Excluding the intersection is the same as the union of the exclusions.
--
--     > @0 prop-excluding-intersection
--     >   : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--     >   → (Set.intersection x y) ⋪ utxo ≡ (x ⋪ utxo) ∪ (y ⋪ utxo)

-- $prop-excluding-sym
-- #p:prop-excluding-sym#
--
-- [prop-excluding-sym]:
--
--     Excluding two sets of 'TxIn's can be done in either order.
--
--     > prop-excluding-sym
--     >   : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
--     >   → x ⋪ (y ⋪ utxo) ≡ y ⋪ (x ⋪ utxo)

-- $prop-excluding-union
-- #p:prop-excluding-union#
--
-- [prop-excluding-union]:
--
--     Excluding from a union is the same as excluding
--     from each member of the union.
--
--     > prop-excluding-union
--     >   : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
--     >   → x ⋪ (ua ∪ ub) ≡ (x ⋪ ua) ∪ (x ⋪ ub)

-- $prop-excludingS
-- #p:prop-excludingS#
--
-- [prop-excludingS]:
--     Specification of 'excludingS':
--     Set difference with the domain of the 'UTxO'.
--
--     > prop-excludingS
--     >   : ∀ {x : Set.ℙ TxIn} {utxo : UTxO}
--     >   → excludingS x utxo
--     >     ≡ Set.difference x (dom utxo)

-- $prop-filterByAddress-filters
-- #p:prop-filterByAddress-filters#
--
-- [prop-filterByAddress-filters]:
--
--     Those outputs whose address satisfies the predicate are kept.
--
--     > prop-filterByAddress-filters
--     >     : ∀ (p : Address → Bool)
--     >         (utxo : UTxO) (txin : TxIn) (txout : TxOut)
--     >     → Map.lookup txin utxo ≡ Just txout
--     >     → Map.member txin (filterByAddress p utxo)
--     >         ≡ p (getCompactAddr txout)

-- $prop-restrictedBy-disjoint
-- #p:prop-restrictedBy-disjoint#
--
-- [prop-restrictedBy-disjoint]:
--
--     Restricting to a set that has nothing common in common
--     will give the empty 'UTxO'.
--
--     > prop-restrictedBy-disjoint
--     >   : ∀ {x : Set.ℙ TxIn} {utxo : UTxO}
--     >   → Set.disjoint x (dom utxo) ≡ True
--     >   → restrictedBy utxo x ≡ empty

-- $prop-restrictedBy-dom
-- #p:prop-restrictedBy-dom#
--
-- [prop-restrictedBy-dom]:
--
--     Restricting to the entire domain does nothing.
--
--     > prop-restrictedBy-dom
--     >   : ∀ {utxo : UTxO}
--     >   → restrictedBy utxo (dom utxo) ≡ utxo

-- $prop-restrictedBy-union
-- #p:prop-restrictedBy-union#
--
-- [prop-restrictedBy-union]:
--
--     Restricting a union is the same as restricting
--     from each member of the union.
--
--     > prop-restrictedBy-union
--     >   : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
--     >   → x ⊲ (ua ∪ ub) ≡ (x ⊲ ua) ∪ (x ⊲ ub)

-- $prop-union-assoc
-- #p:prop-union-assoc#
--
-- [prop-union-assoc]:
--
--     'union' is associative.
--
--     > prop-union-assoc
--     >   : ∀ {ua ub uc : UTxO}
--     >   → (ua ∪ ub) ∪ uc ≡ ua ∪ (ub ∪ uc)

-- $prop-union-empty-left
-- #p:prop-union-empty-left#
--
-- [prop-union-empty-left]:
--
--     'empty' is a left identity of 'union'.
--
--     > prop-union-empty-left
--     >   : ∀ {utxo : UTxO}
--     >   → empty ∪ utxo ≡ utxo

-- $prop-union-empty-right
-- #p:prop-union-empty-right#
--
-- [prop-union-empty-right]:
--
--     'empty' is a right identity of 'union'.
--
--     > prop-union-empty-right
--     >   : ∀ {utxo : UTxO}
--     >   → utxo ∪ empty ≡ utxo

-- $prop-union-restrictedBy-absorbs
-- #p:prop-union-restrictedBy-absorbs#
--
-- [prop-union-restrictedBy-absorbs]:
--
--     Since 'union' is left-biased,
--     taking the union with a 'UTxO' whose domain is a subset
--     does nothing.
--
--     > prop-union-restrictedBy-absorbs
--     >   : ∀ {ua ub : UTxO}
--     >   → ua ∪ (dom ua ⊲ ub) ≡ ua

-- $prop-union-sym
-- #p:prop-union-sym#
--
-- [prop-union-sym]:
--
--     'union' is symmetric /if/ the 'UTxO' are disjoint.
--
--     > prop-union-sym
--     >   : ∀ {ua ub : UTxO}
--     >   → disjoint ua ub ≡ True
--     >   → ua ∪ ub ≡ ub ∪ ua
