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
open import Haskell.Data.InverseMap using
    ( InverseMap
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

import Haskell.Data.InverseMap as InverseMap
import Haskell.Data.Map as Map
import Haskell.Data.Maps.PairMap as PairMap
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
    Helpers
------------------------------------------------------------------------------}

-- | Insert a set of keys into a 'Map' that all have the same value.
insertManyKeys
    : ∀ {key v : Set} {{_ : Ord key}} {{_ : Ord v}}
    → ℙ key → v → Map key v → Map key v
insertManyKeys keys v m0 =
    foldl' (\m key → Map.insert key v m) m0 keys

{-# COMPILE AGDA2HS insertManyKeys #-}

{-----------------------------------------------------------------------------
    Introduction
------------------------------------------------------------------------------}
empty : TxHistory
empty = record
  { txSlotsByTxId = Map.empty
  ; txSlotsBySlot = Map.empty
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
    txs2 = Map.restrictKeys txSlotsByTxId txs1

-- | Get the total 'ValueTransfer' in a given slot range.
getValueTransfers
  : (Slot × Slot) → TxHistory → Map Address ValueTransfer
getValueTransfers (from , to) history =
    foldl' (Map.unionWith (_<>_)) Map.empty txs2
  where
    open TxHistory history
    onlyFuture = Map.dropWhileAntitone (_<= from) txSlotsBySlot

    txs1 : ℙ TxId
    txs1 = foldMap id (Map.takeWhileAntitone (_<= to) txSlotsBySlot)

    txs2 : List (Map Address ValueTransfer)
    txs2 = map (λ tx → PairMap.lookupA tx txTransfers) (toList txs1)

{-# COMPILE AGDA2HS getTip #-}
{-# COMPILE AGDA2HS getAddressHistory #-}
{-# COMPILE AGDA2HS getValueTransfers #-}

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}

rollForward : SlotNo → List (TxId × ResolvedTx) → TxHistory → TxHistory
rollForward new txs history =
    if WithOrigin.At new <= getTip history
    then history
    else record
        { txSlotsBySlot = InverseMap.insertManyKeys txids slot txSlotsBySlot
        ; txSlotsByTxId = insertManyKeys txids slot txSlotsByTxId
        ; txTransfers = foldl' insertValueTransfer txTransfers txs
        ; tip = WithOrigin.At new
        }
  where
    open TxHistory history

    slot = WithOrigin.At new
    txids = Set.fromList (map fst txs)

    insertValueTransfer
      : PairMap.PairMap TxId Address ValueTransfer
      → TxId × ResolvedTx
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
        { txSlotsBySlot = leftSlots
        ; txSlotsByTxId = Map.withoutKeys txSlotsByTxId rolledTxIds
        ; txTransfers = PairMap.withoutKeysA txTransfers rolledTxIds
        ; tip = new
        }
  where 
    open TxHistory history
    spanSlots = Map.spanAntitone (_<= new) txSlotsBySlot
    leftSlots = fst spanSlots
    rolledSlots = snd spanSlots
    rolledTxIds =
        foldMap id rolledSlots

{-# COMPILE AGDA2HS rollForward #-}
{-# COMPILE AGDA2HS rollBackward #-}
