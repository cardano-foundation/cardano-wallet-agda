{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.TxHistory.Type where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; Slot
    ; TxId
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( ValueTransfer
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Maps.PairMap using
    ( PairMap
    )
open import Haskell.Data.Maps.Timeline using
    ( Timeline
    )

{-----------------------------------------------------------------------------
    Data type
------------------------------------------------------------------------------}

{-| Tx History.

History of the transactions to and from the Deposit Wallet.
Information includes:

* Slot of each transaction
* Value transfer for each transaction, indexed by address

-}
record TxHistory : Set where
  field
    txIds : Timeline Slot TxId

    txTransfers : PairMap TxId Address ValueTransfer
        -- ^ Map from (transaction × address) to ValueTransfer

    tip : Slot
        -- ^ Current tip slot.

open TxHistory public

{-# COMPILE AGDA2HS TxHistory #-}
