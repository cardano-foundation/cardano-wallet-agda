{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.UTxO
    {-
    ; UTxO
    -}
    where

open import Haskell.Prelude hiding (null)

open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; TxIn
    ; TxOut
    ; Value
    )

import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    UTxO
------------------------------------------------------------------------------}

UTxO = Map.Map TxIn TxOut

null : UTxO → Bool
null = Map.null

empty : UTxO
empty = Map.empty

-- | Domain of a 'UTxO' = the set of /inputs/ of the /utxo/.
dom : UTxO → Set.ℙ TxIn
dom = Map.keysSet

balance : UTxO → Value
balance = foldMap TxOut.value

-- | Left-biased union.
union : UTxO → UTxO → UTxO
union = Map.unionWith (λ x y → x)

excluding : UTxO → Set.ℙ TxIn → UTxO
excluding = Map.withoutKeys

-- | Exclude the inputs of a 'UTxO' from a 'Set' of inputs.
excludingS : Set.ℙ TxIn → UTxO → Set.ℙ TxIn
excludingS s utxo = Set.filter (not ∘ (λ txin → Map.member txin utxo)) s

filterByAddress : (Address → Bool) → UTxO → UTxO
filterByAddress p = Map.filter (p ∘ TxOut.address)
