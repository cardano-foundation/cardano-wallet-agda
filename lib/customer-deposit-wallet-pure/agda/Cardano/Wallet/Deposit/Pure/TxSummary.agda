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
{-|
A 'TxSummary' summarizes a transaction.

Note: Haddock may be broken. The fields of this record
refer to types from "Cardano.Wallet.Read".
-}
record TxSummary : Set where
  field
    txSummarized : TxId
    txChainPoint : ChainPoint
    txTransfer   : ValueTransfer

open TxSummary public

-- | Create a 'TxSummary' from a transaction.
--
-- FIXME: This is a mock summary for now!
mkTxSummary : ∀ {era} → {{IsEra era}} → Tx era → ValueTransfer → TxSummary
mkTxSummary = λ tx transfer' → record
    { txSummarized = getTxId tx
    ; txChainPoint = ChainPoint.GenesisPoint
    ; txTransfer = transfer'
    }

{-# COMPILE AGDA2HS TxSummary #-}
{-# COMPILE AGDA2HS mkTxSummary #-}
