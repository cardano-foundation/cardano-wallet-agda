{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.TxHistory.Type where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( ValueTransfer
    )
open import Cardano.Wallet.Deposit.Read.Temp using
    ( Address
    )
open import Cardano.Wallet.Read using
    ( ChainPoint
    ; Slot
    ; TxId
    )
open import Data.Maps.PairMap using
    ( PairMap
    )
open import Data.Maps.Timeline using
    ( Timeline
    )
open import Haskell.Data.Map using
    ( Map
    )

{-# FOREIGN AGDA2HS
{-# LANGUAGE StrictData #-}
#-}

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read
    ( ChainPoint (..)
    , Slot
    , TxId
    )
import Data.Map (Map)
#-}

{-----------------------------------------------------------------------------
    Data type
------------------------------------------------------------------------------}

{-| 'TxHistory'.

History of the transactions to and from the Deposit Wallet.
Information includes:

* Slot of each transaction
* Value transfer for each transaction, indexed by address

NOTE: This is an abstract data type,
its internals are only exported for technical reasons.
-}
record TxHistory : Set where
  field
    txIds : Timeline Slot TxId

    txBlocks : Map TxId ChainPoint
        -- ^ Map from transaction to the respective 'ChainPoint'.

    txTransfers : PairMap TxId Address ValueTransfer
        -- ^ Map from (transaction × address) to ValueTransfer

    tip : Slot
        -- ^ Current tip slot.

open TxHistory public

{-# COMPILE AGDA2HS TxHistory #-}
