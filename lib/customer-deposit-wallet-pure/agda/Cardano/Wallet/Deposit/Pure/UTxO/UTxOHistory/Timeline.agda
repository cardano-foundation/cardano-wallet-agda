-- |
-- Implementation of 'TimelineUTxO'.
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Timeline
    {-|
      -- * TimelineUTxO
    ; TimelineUTxO (..)
    ; getUTxO
    ; fromOrigin

      -- * Operations
    ; insertDeltaUTxO
    ; dropAfter
    ; pruneBefore

      -- * Internal
    ; getSpent
    -}
    where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO using
    ( DeltaUTxO
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    ; dom
    ; excluding
    ; _⋪_
    ; _⊲_
    ; _∪_
    )
open import Cardano.Wallet.Read using
    ( Slot
    ; SlotNo
    ; TxIn
    ; WithOrigin
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Maps.Timeline using
    ( Timeline
    )
open import Haskell.Data.Set using
    ( ℙ
    )

import Cardano.Wallet.Deposit.Pure.RollbackWindow as RollbackWindow
import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO as DeltaUTxO
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Haskell.Data.Map as Map
import Haskell.Data.Maps.Timeline as Timeline
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    Type
------------------------------------------------------------------------------}

-- | 'TimelineUTxO' represents a timeline of changes to the 'UTxO' set.
--
-- We keep track of the creation
-- and spending of slot of each TxIn.
-- This allows us to rollback to a given slot
-- and prune to a given slot.
record TimelineUTxO : Set where
  field
    history : UTxO
        -- ^ All UTxO , spent and unspent.
    created : Timeline Slot TxIn
        -- ^ Creation slots of the TxIn, spent and unspent.
    spent : Timeline SlotNo TxIn
        -- ^ Spending slot number of the TxIn, spent.
    boot : UTxO
        -- ^ UTxO created at genesis.

open TimelineUTxO public

{-# COMPILE AGDA2HS TimelineUTxO #-}

{-----------------------------------------------------------------------------
    Functions
------------------------------------------------------------------------------}

-- | Apply all changes to the 'UTxO'.
getUTxO : TimelineUTxO → UTxO
getUTxO us = excluding (history us) (Timeline.items (spent us))

{-# COMPILE AGDA2HS getUTxO #-}

-- | The spent 'TxIn's that can be rolled back.
--
-- (Internal, exported for specification.)
getSpent : TimelineUTxO → Map TxIn SlotNo
getSpent = Timeline.getMapTime ∘ spent

{-# COMPILE AGDA2HS getSpent #-}

-- | An empty 'TimelineUTxO'.
fromOrigin : UTxO → TimelineUTxO
fromOrigin utxo = record
    { history = utxo
    ; created =
        Timeline.insertMany WithOrigin.Origin (dom utxo)
        (Timeline.empty)
    ; spent = Timeline.empty
    ; boot = utxo
    }

{-# COMPILE AGDA2HS fromOrigin #-}

-- | Insert a 'UTxO' change at a specific slot.
insertDeltaUTxO
  : SlotNo → DeltaUTxO → TimelineUTxO → TimelineUTxO
insertDeltaUTxO newTip delta old = record
    { history = UTxO.union (history old) (DeltaUTxO.received delta)
    ; created =
        Timeline.insertMany
            (WithOrigin.At newTip) receivedTxIns (created old)
    ; spent =
        Timeline.insertMany
            newTip excludedTxIns (spent old)
    ; boot = boot old
    }
  where
    receivedTxIns =
        Set.difference
            (dom (DeltaUTxO.received delta))
            (dom (history old))
    excludedTxIns =
        Set.difference
            (Set.intersection (DeltaUTxO.excluded delta) (dom (history old)))
            (Timeline.items (spent old))

{-# COMPILE AGDA2HS insertDeltaUTxO #-}

-- | Helper for 'dropAfter'.
dropAfterSpent
  : Slot → Timeline.Timeline SlotNo TxIn → Timeline.Timeline SlotNo TxIn
dropAfterSpent WithOrigin.Origin spents = Timeline.empty
dropAfterSpent (WithOrigin.At slot) spents = Timeline.dropAfter slot spents

-- | Drop all 'UTxO' changes after a given slot.
dropAfter
  : Slot → TimelineUTxO → TimelineUTxO
dropAfter newTip old = record
    { history = excluding (history old) rolledCreated
    ; created = created'
    ; spent = dropAfterSpent newTip (spent old)
    ; boot = boot old
    }
  where
    deletedAfter = Timeline.deleteAfter newTip (created old)
    rolledCreated = fst deletedAfter
    created' = snd deletedAfter

{-# COMPILE AGDA2HS dropAfterSpent #-}
{-# COMPILE AGDA2HS dropAfter #-}

{-|
Combine all changes before the given 'SlotNo'.

Using 'prune' will free up some space as old information
can be summarized and discarded.
-}
pruneBefore : SlotNo → TimelineUTxO → TimelineUTxO
pruneBefore newFinality old = record
    { history = excluding (history old) prunedTxIns
    ; created = Timeline.difference (created old) prunedTxIns
    ; spent = spent1
    ; boot = boot old
    }
  where
    pruned = Timeline.dropWhileAntitone (_<= newFinality) (spent old)
    prunedTxIns = fst pruned
    spent1 = snd pruned

{-# COMPILE AGDA2HS pruneBefore #-}
