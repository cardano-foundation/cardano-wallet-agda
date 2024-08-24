{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.TxHistory.Core where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; Slot
    ; SlotNo
    ; TxId
    ; WithOrigin
    ; IsEra
    )
open import Cardano.Wallet.Deposit.Pure.TxHistory.Type using
    ( TxHistory
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.Tx using
    ( ResolvedTx 
    ; valueTransferFromResolvedTx
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( ValueTransfer
    )
open import Haskell.Data.List using
    ( foldl'
    ; sortOn
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Set using
    ( ℙ
    )

import Haskell.Data.Map as Map
import Haskell.Data.Maps.PairMap as PairMap
import Haskell.Data.Maps.Timeline as Timeline
import Haskell.Data.Set as Set

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.TxHistory.Type
    ( TxHistory (..)
    )
import Data.Foldable
    ( toList
    )
#-}

{-----------------------------------------------------------------------------
    Introduction
------------------------------------------------------------------------------}
empty : TxHistory
empty = record
  { txIds = Timeline.empty
  ; txTransfers = PairMap.empty
  ; tip = WithOrigin.Origin
  }

{-# COMPILE AGDA2HS empty #-}

{-----------------------------------------------------------------------------
    Observation
------------------------------------------------------------------------------}

-- | Returns the tip slot.
getTip : TxHistory → Slot
getTip = TxHistory.tip

-- | Get the transaction history for a single address.
getAddressHistory
  : Address → TxHistory → List (Slot × TxId)
getAddressHistory address history =
    sortOn fst (map (λ {(x , y) → (y , x)}) (Map.toAscList txs2))
  where
    open TxHistory history

    txs1 : ℙ TxId
    txs1 = Map.keysSet (PairMap.lookupB address txTransfers)

    txs2 : Map TxId Slot
    txs2 = Map.restrictKeys (Timeline.getMapTime txIds) txs1

-- | Get the total 'ValueTransfer' in a given slot range.
getValueTransfers
  : (Slot × Slot) → TxHistory → Map Address ValueTransfer
getValueTransfers range history =
    foldl' (Map.unionWith (_<>_)) Map.empty txs2
  where
    open TxHistory history

    txs1 : ℙ TxId
    txs1 =
        Map.keysSet
            (Timeline.getMapTime (Timeline.restrictRange range txIds))

    txs2 : List (Map Address ValueTransfer)
    txs2 = map (λ tx → PairMap.lookupA tx txTransfers) (toList txs1)

{-# COMPILE AGDA2HS getTip #-}
{-# COMPILE AGDA2HS getAddressHistory #-}
{-# COMPILE AGDA2HS getValueTransfers #-}

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}

rollForward
  : ∀{era} → {{IsEra era}}
  → SlotNo → List (TxId × ResolvedTx era) → TxHistory → TxHistory
rollForward {era} new txs history =
    if WithOrigin.At new <= getTip history
    then history
    else record
        { txIds = Timeline.insertMany slot txids txIds
        ; txTransfers = foldl' insertValueTransfer txTransfers txs
        ; tip = WithOrigin.At new
        }
  where
    open TxHistory history

    slot = WithOrigin.At new
    txids = Set.fromList (map fst txs)

    insertValueTransfer
      : ∀{era1} → {{IsEra era1}}
      → PairMap.PairMap TxId Address ValueTransfer
      → TxId × ResolvedTx era1
      → PairMap.PairMap TxId Address ValueTransfer
    insertValueTransfer m0 (txid , tx) =
        foldl' (uncurry ∘ fun) m0 (Map.toAscList mv)
      where
        mv = valueTransferFromResolvedTx tx
        fun = λ m addr v → PairMap.insert txid addr v m

rollBackward : Slot → TxHistory → TxHistory
rollBackward new history = 
    if new > getTip history
    then history
    else record
        { txIds = keptTimeline
        ; txTransfers = PairMap.withoutKeysA txTransfers deletedTxIds
        ; tip = new
        }
  where 
    open TxHistory history

    deleteAfterTxIds = Timeline.deleteAfter new txIds
    deletedTxIds = fst deleteAfterTxIds
    keptTimeline = snd deleteAfterTxIds

{-# COMPILE AGDA2HS rollForward #-}
{-# COMPILE AGDA2HS rollBackward #-}
