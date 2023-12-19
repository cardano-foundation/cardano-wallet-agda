{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.Balance where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Pure.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Pure.DeltaUTxO using
    ( DeltaUTxO
    )
open import Cardano.Wallet.Deposit.Read using
    ( Tx
    )

import Cardano.Wallet.Deposit.Pure.DeltaUTxO as DeltaUTxO
import Cardano.Wallet.Deposit.Pure.UTxO as UTxO
import Cardano.Wallet.Deposit.Read as Read
import Haskell.Data.Map as Map

{-----------------------------------------------------------------------------
    UTxO utilities
------------------------------------------------------------------------------}
-- | Remove unspent outputs that are consumed by the given transaction.
spendTxD : Read.Tx -> UTxO -> (DeltaUTxO × UTxO)
spendTxD tx u =
    DeltaUTxO.excludingD u inputsToExclude
  where
    inputsToExclude = Read.Tx.inputs tx

-- | Convert the transaction outputs into a 'UTxO' set.
utxoFromTxOutputs : Read.Tx → UTxO
utxoFromTxOutputs tx = Map.fromList $ zip txins txouts
  where
    n = length (Tx.outputs tx)
    txins = map (λ j → (Tx.txid tx , j)) $ enumFromTo 0 (n - 1)
    txouts = Tx.outputs tx

{-----------------------------------------------------------------------------
    Applying Blocks
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

