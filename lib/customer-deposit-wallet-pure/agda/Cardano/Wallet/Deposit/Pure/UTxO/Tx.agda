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
    ( IsEra
    ; IsValid
      ; IsValidC
    ; Tx
      ; utxoFromEraTx
      ; getInputs
      ; getCollateralInputs
      ; getScriptValidity
    ; TxIn
    ; TxOut
      ; getCompactAddr
      ; getValue
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
spendTxD : ∀{era} → {{IsEra era}} → Read.Tx era → UTxO → (DeltaUTxO × UTxO)
spendTxD tx u =
    DeltaUTxO.excludingD u inputsToExclude
  where
    inputsToExclude : Set.ℙ TxIn
    inputsToExclude =
        case (getScriptValidity tx) of λ
          { (IsValidC True) → getInputs tx
          ; (IsValidC False) → getCollateralInputs tx
          }

-- | Convert the transaction outputs into a 'UTxO' set.
utxoFromTxOutputs : ∀{era} → {{IsEra era}} → Read.Tx era → UTxO
utxoFromTxOutputs = utxoFromEraTx

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
    : ∀ {era} → {{IsEra era}}
    → IsOurs Read.Addr
    -> Read.Tx era
    -> UTxO
    -> (DeltaUTxO × UTxO)
applyTx isOurs tx u0 =
    let (du10 , u1)  = spendTxD tx u0
        receivedUTxO = UTxO.filterByAddress isOurs (utxoFromTxOutputs tx)
        (du21 , u2)  = DeltaUTxO.receiveD u1 receivedUTxO
        (du , u) = (DeltaUTxO.append du21 du10 , u2)
    
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
          then (DeltaUTxO.empty , u0)
          else (du , u)

{-# COMPILE AGDA2HS IsOurs #-}
{-# COMPILE AGDA2HS applyTx #-}

{-----------------------------------------------------------------------------
    Resolve Inputs
------------------------------------------------------------------------------}
-- | A transaction whose inputs have been partially resolved.
record ResolvedTx era : Set where
  field
    resolvedTx : Read.Tx era
    resolvedInputs : UTxO

open ResolvedTx public

resolveInputs : ∀{era} → {{IsEra era}} → UTxO → Read.Tx era → ResolvedTx era
resolveInputs utxo tx =
  record
    { resolvedTx = tx
    ; resolvedInputs =
        UTxO.restrictedBy
            utxo
            (getInputs tx)
    }

{-# COMPILE AGDA2HS ResolvedTx #-}
{-# COMPILE AGDA2HS resolveInputs #-}

{-----------------------------------------------------------------------------
    ValueTransfer
------------------------------------------------------------------------------}
-- Helper function
pairFromTxOut : Read.TxOut → (Read.Address × Read.Value)
pairFromTxOut =
    λ txout → (getCompactAddr txout , getValue txout)

-- | Compute how much 'Value' a 'UTxO' set contains at each address.
groupByAddress : UTxO → Map.Map Read.Address Read.Value
groupByAddress =
    Map.fromListWith (_<>_) ∘ map pairFromTxOut ∘ Map.elems

-- | Compute the 'ValueTransfer' corresponding to 'DeltaUTxO'.
valueTransferFromDeltaUTxO
  : UTxO
    -- ^ UTxO set to which the 'DeltaUTxO' is applied.
  → DeltaUTxO
    -- ^ Change to the 'UTxO' set.
  → Map.Map Read.Address ValueTransfer
    -- ^ Value transfer, grouped by address.
valueTransferFromDeltaUTxO u0 du =
    Map.unionWith (_<>_) ins outs
  where
    u1 = UTxO.restrictedBy u0 (DeltaUTxO.excluded du)

    ins  = Map.map fromSpent (groupByAddress u1)
    outs = Map.map fromReceived (groupByAddress (DeltaUTxO.received du))

-- | Compute the 'ValueTransfer' corresponding to a 'ResolvedTx'.
-- Spent transaction outputs that have not been resolved will not
-- be considered.
valueTransferFromResolvedTx
    : ∀{era} → {{IsEra era}}
    → ResolvedTx era → Map.Map Read.Address ValueTransfer
valueTransferFromResolvedTx tx =
    valueTransferFromDeltaUTxO u0 du
  where
    u0 = resolvedInputs tx
    du = fst (applyTx (λ _ → True) (resolvedTx tx) u0)

{-# COMPILE AGDA2HS pairFromTxOut #-}
{-# COMPILE AGDA2HS groupByAddress #-}
{-# COMPILE AGDA2HS valueTransferFromDeltaUTxO #-}
{-# COMPILE AGDA2HS valueTransferFromResolvedTx #-}
