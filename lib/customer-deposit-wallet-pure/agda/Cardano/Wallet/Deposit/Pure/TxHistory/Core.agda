{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.TxHistory.Core where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; ChainPoint
      ; slotFromChainPoint
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
{-|
The empty transaction history.
It starts at genesis and contains no transactions.
-}
empty : TxHistory
empty = record
  { txIds = Timeline.empty
  ; txBlocks = Map.empty
  ; txTransfers = PairMap.empty
  ; tip = WithOrigin.Origin
  }

{-# COMPILE AGDA2HS empty #-}

{-----------------------------------------------------------------------------
    Observation
------------------------------------------------------------------------------}

{-|
'getTip' records the slot up to which the transaction history
includes information from blocks. All blocks from genesis up to and
including this slot have been inspected for relevant transactions.
-}
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

{-|
Include the information contained in the block at 'SlotNo'
into the transaction history.
We expect that the block has already been digested into a list
of 'ResolvedTx'.
-}
rollForward
  : ∀{era} → {{IsEra era}}
  → ChainPoint → List (TxId × ResolvedTx era) → TxHistory → TxHistory
rollForward {era} newTip txs history =
    if newSlot <= getTip history
    then history
    else record
        { txIds = Timeline.insertMany newSlot txids txIds
        ; txBlocks = Timeline.insertManyKeys txids newTip txBlocks
        ; txTransfers = foldl' insertValueTransfer txTransfers txs
        ; tip = newSlot
        }
  where
    open TxHistory history

    newSlot = slotFromChainPoint newTip
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

{-|
Roll back the transaction history to the given 'Slot',
i.e. forget about all transaction that are strictly later than this slot.
-}
rollBackward : Slot → TxHistory → TxHistory
rollBackward new history = 
    if new > getTip history
    then history
    else record
        { txIds = keptTimeline
        ; txBlocks = Map.withoutKeys txBlocks deletedTxIds
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
