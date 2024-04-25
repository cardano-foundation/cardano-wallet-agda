{-# OPTIONS --erasure #-}

-- | Applying transactions to a UTxO set.
module Cardano.Wallet.Deposit.Pure.UTxO.Tx where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO using
    ( DeltaUTxO
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( ValueTransfer
    ; fromReceived
    ; fromSpent
    )
open import Cardano.Wallet.Deposit.Read using
    ( Tx
    ; TxBody
    )

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO as DeltaUTxO
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Cardano.Wallet.Deposit.Read as Read
import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    UTxO utilities
------------------------------------------------------------------------------}
-- | Remove unspent outputs that are consumed by the given transaction.
spendTxD : Read.Tx -> UTxO -> (DeltaUTxO × UTxO)
spendTxD tx u =
    DeltaUTxO.excludingD u inputsToExclude
  where
    inputsToExclude = Set.fromList (TxBody.inputs (Tx.txbody tx))

-- | Convert the transaction outputs into a 'UTxO' set.
utxoFromTxOutputs : Read.Tx → UTxO
utxoFromTxOutputs tx = Map.fromList $ zip txins txouts
  where
    n = length (TxBody.outputs (Tx.txbody tx))
    txins = map (λ j → (Tx.txid tx , j)) $ enumFromTo 0 (n - 1)
    txouts = TxBody.outputs (Tx.txbody tx)

{-# COMPILE AGDA2HS spendTxD #-}
{-# COMPILE AGDA2HS utxoFromTxOutputs #-}

{-----------------------------------------------------------------------------
    Apply Transactions
------------------------------------------------------------------------------}
IsOurs : Set → Set
IsOurs addr = addr -> Bool

-- | Apply a transactions to the 'UTxO'.
--
-- Returns both a delta and the new value.
applyTx
    : IsOurs Read.Addr -> Read.Tx -> UTxO -> (DeltaUTxO × UTxO)
applyTx isOurs tx u0 =
    let (du10 , u1)  = spendTxD tx u0
        receivedUTxO = UTxO.filterByAddress isOurs (utxoFromTxOutputs tx)
        (du21 , u2)  = DeltaUTxO.receiveD u1 receivedUTxO
        (du , u) = (du21 <> du10 , u2)
    
        -- NOTE: Performance.
        -- 'applyTx' is part of a tight loop that inspects all transactions
        -- (> 30M Txs as of Feb 2022).
        -- Thus, we make a small performance optimization here.
        -- Specifically, we want to reject a transaction as soon as possible
        -- if it does not change the 'UTxO' set. The test
        isUnchangedUTxO = UTxO.null receivedUTxO && DeltaUTxO.null du10
        -- allocates slightly fewer new Set/Map than the definition
        --   isUnchangedUTxO =  mempty == du

    in  if isUnchangedUTxO
          then (mempty , u0)
          else (du , u)

{-# COMPILE AGDA2HS IsOurs #-}
{-# COMPILE AGDA2HS applyTx #-}

{-----------------------------------------------------------------------------
    Resolve Inputs
------------------------------------------------------------------------------}
-- | A transaction whose inputs have been partially resolved.
record ResolvedTx : Set where
  field
    resolvedTx : Read.Tx
    resolvedInputs : UTxO

open ResolvedTx public

resolveInputs : UTxO → Read.Tx → ResolvedTx
resolveInputs utxo tx =
  record
    { resolvedTx = tx
    ; resolvedInputs =
        UTxO.restrictedBy
            utxo
            (Set.fromList (TxBody.inputs (Tx.txbody tx)))
    }

{-# COMPILE AGDA2HS ResolvedTx #-}
{-# COMPILE AGDA2HS resolveInputs #-}

{-----------------------------------------------------------------------------
    ValueTransfer
------------------------------------------------------------------------------}
-- Helper function
pairFromTxOut : Read.TxOut → (Read.Address × Read.Value)
pairFromTxOut =
    λ txout → (Read.TxOut.address txout , Read.TxOut.value txout)

-- | Compute how much 'Value' a 'UTxO' set contains at each address.
groupByAddress : UTxO → Map.Map Read.Address Read.Value
groupByAddress =
    Map.fromListWith (_<>_) ∘ map pairFromTxOut ∘ Map.elems

-- | Compute the 'ValueTransfer' corresponding to 'DeltaUTxO'.
computeValueTransfer
  : UTxO
    -- ^ UTxO set to which the 'DeltaUTxO' is applied.
  → DeltaUTxO
    -- ^ Change to the 'UTxO' set.
  → Map.Map Read.Address ValueTransfer
    -- ^ Value transfer, grouped by address.
computeValueTransfer u0 du =
    Map.unionWith (_<>_) ins outs
  where
    u1 = UTxO.restrictedBy u0 (DeltaUTxO.excluded du)

    ins  = Map.map fromSpent (groupByAddress u1)
    outs = Map.map fromReceived (groupByAddress (DeltaUTxO.received du))

{-# COMPILE AGDA2HS pairFromTxOut #-}
{-# COMPILE AGDA2HS groupByAddress #-}
{-# COMPILE AGDA2HS computeValueTransfer #-}
