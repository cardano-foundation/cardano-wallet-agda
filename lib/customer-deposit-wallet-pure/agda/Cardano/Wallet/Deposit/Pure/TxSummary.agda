module Cardano.Wallet.Deposit.Pure.TxSummary where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( ValueTransfer
    )
open import Cardano.Wallet.Deposit.Read using
    ( IsEra
    ; Tx
      ; getTxId
    ; TxId
    ; ChainPoint
    )

import Cardano.Wallet.Deposit.Read as Read

{-----------------------------------------------------------------------------
    TxSummary
------------------------------------------------------------------------------}

record TxSummary : Set where
  field
    summarizedTx : TxId
    point : ChainPoint
    transfer : ValueTransfer

open TxSummary public

-- This is a mock summary for now
mkTxSummary : ∀ {era} → {{IsEra era}} → Tx era → ValueTransfer → TxSummary
mkTxSummary = λ tx transfer' → record
    { summarizedTx = getTxId tx
    ; point = ChainPoint.GenesisPoint
    ; transfer = transfer'
    }

{-# COMPILE AGDA2HS TxSummary #-}
{-# COMPILE AGDA2HS mkTxSummary #-}
