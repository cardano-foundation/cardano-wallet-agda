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

balance : UTxO → Value
balance = foldMap TxOut.value

-- | Left-biased union.
union : UTxO → UTxO → UTxO
union = Map.unionWith (λ x y → x)

excluding : UTxO → Set.ℙ TxIn → UTxO
excluding = Map.withoutKeys

postulate
  filterByAddress : (Address → Bool) → UTxO → UTxO
