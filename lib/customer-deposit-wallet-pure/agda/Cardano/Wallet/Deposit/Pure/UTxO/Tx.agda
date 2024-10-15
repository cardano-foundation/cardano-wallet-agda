{-# OPTIONS --erasure #-}

-- | Applying transactions to a UTxO set.
module Cardano.Wallet.Deposit.Pure.UTxO.Tx
  {-|
  -- * Applying Transactions to UTxO
  ; IsOurs
  ; applyTx

  -- * Resolved Transactions
  ; ResolvedTx (..)
  ; resolveInputs
  
  -- * Value transfer from transactions
  ; valueTransferFromDeltaUTxO
  ; valueTransferFromResolvedTx
  -} where

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
open import Cardano.Wallet.Read using
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
    )

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO as DeltaUTxO
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Cardano.Wallet.Read as Read
import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    UTxO utilities
------------------------------------------------------------------------------}
-- | Remove unspent outputs that are consumed by the given transaction.
-- Also returns a delta.
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

-- | Convert the transaction outputs into a 'UTxO'.
utxoFromTxOutputs : ∀{era} → {{IsEra era}} → Read.Tx era → UTxO
utxoFromTxOutputs = utxoFromEraTx

{-# COMPILE AGDA2HS spendTxD #-}
{-# COMPILE AGDA2HS utxoFromTxOutputs #-}

{-----------------------------------------------------------------------------
    Apply Transactions
------------------------------------------------------------------------------}
-- | Type for a predicate that tests whether @addr@ belongs to us.
IsOurs : Set → Set
IsOurs addr = addr -> Bool

-- | Apply a transactions to the 'UTxO'.
--
-- Returns both a delta and the new value.
applyTx
    : ∀ {era} → {{IsEra era}}
    → IsOurs Read.CompactAddr
    -> Read.Tx era
    -> UTxO
    -> (DeltaUTxO × UTxO)
applyTx isOurs tx u0 =
    if isUnchangedUTxO
        then (DeltaUTxO.empty , u0)
        else (du , u)
  where
    d1 = spendTxD tx u0
    du10 = fst d1
    u1 = snd d1

    receivedUTxO = UTxO.filterByAddress isOurs (utxoFromTxOutputs tx)
    d2 = DeltaUTxO.receiveD u1 receivedUTxO
    du21 = fst d2
    u2 = snd d2

    du = DeltaUTxO.append du21 du10
    u = u2

    -- NOTE: Performance.
    -- 'applyTx' is part of a tight loop that inspects all transactions
    -- (> 30M Txs as of Feb 2022).
    -- Thus, we make a small performance optimization here.
    -- Specifically, we want to reject a transaction as soon as possible
    -- if it does not change the 'UTxO' set. The test
    isUnchangedUTxO = UTxO.null receivedUTxO && DeltaUTxO.null du10
    -- allocates slightly fewer new Set/Map than the definition
    --   isUnchangedUTxO = UTxO.null du

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

-- | Resolve transaction inputs by consulting a known 'UTxO' set.
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
-- | Helper function
--
-- (Internal, exported for technical reasons.)
pairFromTxOut : Read.TxOut → (Read.CompactAddr × Read.Value)
pairFromTxOut =
    λ txout → (getCompactAddr txout , getValue txout)

-- | Compute how much 'Value' a 'UTxO' set contains at each address.
groupByAddress : UTxO → Map.Map Read.CompactAddr Read.Value
groupByAddress =
    Map.fromListWith (_<>_) ∘ map pairFromTxOut ∘ Map.elems

-- | Compute the 'ValueTransfer' corresponding to 'DeltaUTxO'.
valueTransferFromDeltaUTxO
  : UTxO
    -- ^ UTxO set to which the 'DeltaUTxO' is applied.
  → DeltaUTxO
    -- ^ Change to the 'UTxO' set.
  → Map.Map Read.CompactAddr ValueTransfer
    -- ^ Value transfer, grouped by address.
valueTransferFromDeltaUTxO u0 du =
    Map.unionWith (_<>_) ins outs
  where
    u1 = UTxO.restrictedBy u0 (DeltaUTxO.excluded du)

    ins  = Map.map fromSpent (groupByAddress u1)
    outs = Map.map fromReceived (groupByAddress (DeltaUTxO.received du))

-- | Compute the 'ValueTransfer' corresponding to a 'ResolvedTx'.
--
-- Caveat: Spent transaction outputs that have not been resolved
-- will be ignored.
valueTransferFromResolvedTx
    : ∀{era} → {{IsEra era}}
    → ResolvedTx era → Map.Map Read.CompactAddr ValueTransfer
valueTransferFromResolvedTx tx =
    valueTransferFromDeltaUTxO u0 du
  where
    u0 = resolvedInputs tx
    du = fst (applyTx (λ _ → True) (resolvedTx tx) u0)

{-# COMPILE AGDA2HS pairFromTxOut #-}
{-# COMPILE AGDA2HS groupByAddress #-}
{-# COMPILE AGDA2HS valueTransferFromDeltaUTxO #-}
{-# COMPILE AGDA2HS valueTransferFromResolvedTx #-}
