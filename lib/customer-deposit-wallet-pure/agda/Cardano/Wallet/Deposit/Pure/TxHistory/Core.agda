{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.TxHistory.Core where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure.TxHistory.Type using
    ( TxHistory
    )
open import Cardano.Wallet.Deposit.Pure.TxSummary using
    ( TxSummary
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.Tx using
    ( ResolvedTx 
    ; valueTransferFromResolvedTx
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( ValueTransfer
    )
open import Cardano.Wallet.Deposit.Read.Temp using
    ( Address
    )
open import Cardano.Wallet.Read using
    ( ChainPoint
      ; slotFromChainPoint
    ; Slot
    ; SlotNo
    ; TxId
    ; WithOrigin
    ; IsEra
    )
open import Data.List using
    ( foldl'
    )
open import Data.Map using
    ( Map
    )
open import Data.Set using
    ( ℙ
    )

import Data.Maps.PairMap as PairMap
import Data.Maps.Timeline as Timeline
import Data.Map as Map
import Data.Set as Set

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.TxHistory.Type
    ( TxHistory (..)
    )
import Data.List
    ( foldl'
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
  : Address → TxHistory → Map TxId TxSummary
getAddressHistory address history =
    txSummaries
  where
    open TxHistory history

    valueTransfers : Map TxId ValueTransfer
    valueTransfers = PairMap.lookupB address txTransfers

    makeTxSummary : TxId → ValueTransfer → Maybe TxSummary
    makeTxSummary txid v =
        case Map.lookup txid txBlocks of λ
            { Nothing → Nothing
            ; (Just b) → Just (record
                { txSummarized = txid
                ; txChainPoint = b
                ; txTransfer = v
                })
            }

    txSummaries : Map TxId TxSummary
    txSummaries = Map.mapMaybeWithKey makeTxSummary valueTransfers

-- | Get the 'ValueTransfer' for each known slot.
getValueTransfers
  : TxHistory → Map Slot (Map Address ValueTransfer)
getValueTransfers history =
    Map.fromListWith (Map.unionWith (_<>_)) transfers 
  where
    open TxHistory history

    timeline : List (Slot × TxId)
    timeline = Timeline.toAscList txIds

    second' : (b → c) → (a × b) → (a × c)
    second' f (x , y) = (x , f y)

    transfers : List (Slot × Map Address ValueTransfer)
    transfers = map (second' (λ txid → PairMap.lookupA txid txTransfers)) timeline

-- | Compute the total 'ValueTransfer' in a given slot range.
getValueTransferInRange
  : (Slot × Slot) → TxHistory → Map Address ValueTransfer
getValueTransferInRange range history =
    foldl' (Map.unionWith (_<>_)) Map.empty txs2
  where
    open TxHistory history

    txs1 : ℙ TxId
    txs1 =
        Timeline.items (Timeline.restrictRange range txIds)

    txs2 : List (Map Address ValueTransfer)
    txs2 = map (λ tx → PairMap.lookupA tx txTransfers) (toList txs1)

{-# COMPILE AGDA2HS getTip #-}
{-# COMPILE AGDA2HS getAddressHistory #-}
{-# COMPILE AGDA2HS getValueTransfers #-}
{-# COMPILE AGDA2HS getValueTransferInRange #-}

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
        mv : Map Address ValueTransfer
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
