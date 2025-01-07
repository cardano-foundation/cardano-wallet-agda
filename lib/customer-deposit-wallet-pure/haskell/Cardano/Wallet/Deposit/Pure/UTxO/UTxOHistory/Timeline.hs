{-# LANGUAGE StrictData #-}

module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Timeline
    ( -- * TimelineUTxO
      TimelineUTxO (..)
    , getUTxO
    , fromOrigin

      -- * Operations
    , insertDeltaUTxO
    , dropAfter
      -- $prop-insertDeltaUTxO-dropAfter-cancel
    , pruneBefore

      -- * Internal
    , getSpent
    )
where

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    ( DeltaUTxO (excluded, received)
    )
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO, dom, excluding)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (union)
import Cardano.Wallet.Read.Block (SlotNo)
import Cardano.Wallet.Read.Chain (Slot, WithOrigin (At, Origin))
import Cardano.Wallet.Read.Tx (TxIn)
import Data.Set (Set)
import Haskell.Data.Map.Def (Map)
import Haskell.Data.Maps.Timeline (Timeline)
import qualified Haskell.Data.Maps.Timeline
    ( deleteAfter
    , difference
    , dropAfter
    , dropWhileAntitone
    , empty
    , getMapTime
    , insertMany
    , items
    )
import qualified Haskell.Data.Set as Set (difference, intersection)
import Prelude hiding (null, subtract)

-- |
-- 'TimelineUTxO' represents a timeline of changes to the 'UTxO' set.
--
-- We keep track of the creation
-- and spending of slot of each TxIn.
-- This allows us to rollback to a given slot
-- and prune to a given slot.
data TimelineUTxO = TimelineUTxO
    { history :: UTxO
    , created :: Timeline Slot TxIn
    , spent :: Timeline SlotNo TxIn
    , boot :: UTxO
    }

-- |
-- Apply all changes to the 'UTxO'.
getUTxO :: TimelineUTxO -> UTxO
getUTxO us =
    excluding
        (history us)
        (Haskell.Data.Maps.Timeline.items (spent us))

-- |
-- The spent 'TxIn's that can be rolled back.
--
-- (Internal, exported for specification.)
getSpent :: TimelineUTxO -> Map TxIn SlotNo
getSpent = Haskell.Data.Maps.Timeline.getMapTime . \r -> spent r

-- |
-- An empty 'TimelineUTxO'.
fromOrigin :: UTxO -> TimelineUTxO
fromOrigin utxo =
    TimelineUTxO
        utxo
        ( Haskell.Data.Maps.Timeline.insertMany
            Origin
            (dom utxo)
            Haskell.Data.Maps.Timeline.empty
        )
        Haskell.Data.Maps.Timeline.empty
        utxo

-- |
-- Insert a 'UTxO' change at a specific slot.
insertDeltaUTxO
    :: SlotNo -> DeltaUTxO -> TimelineUTxO -> TimelineUTxO
insertDeltaUTxO newTip delta old =
    TimelineUTxO
        (UTxO.union (history old) (received delta))
        ( Haskell.Data.Maps.Timeline.insertMany
            (At newTip)
            receivedTxIns
            (created old)
        )
        ( Haskell.Data.Maps.Timeline.insertMany
            newTip
            excludedTxIns
            (spent old)
        )
        (boot old)
  where
    receivedTxIns :: Set TxIn
    receivedTxIns =
        Set.difference (dom (received delta)) (dom (history old))
    excludedTxIns :: Set TxIn
    excludedTxIns =
        Set.difference
            (Set.intersection (excluded delta) (dom (history old)))
            (Haskell.Data.Maps.Timeline.items (spent old))

-- |
-- Helper for 'dropAfter'.
dropAfterSpent
    :: Slot -> Timeline SlotNo TxIn -> Timeline SlotNo TxIn
dropAfterSpent Origin spents = Haskell.Data.Maps.Timeline.empty
dropAfterSpent (At slot) spents =
    Haskell.Data.Maps.Timeline.dropAfter slot spents

-- |
-- Drop all 'UTxO' changes after a given slot.
dropAfter :: Slot -> TimelineUTxO -> TimelineUTxO
dropAfter newTip old =
    TimelineUTxO
        (excluding (history old) rolledCreated)
        created'
        (dropAfterSpent newTip (spent old))
        (boot old)
  where
    deletedAfter :: (Set TxIn, Timeline (WithOrigin SlotNo) TxIn)
    deletedAfter =
        Haskell.Data.Maps.Timeline.deleteAfter newTip (created old)
    rolledCreated :: Set TxIn
    rolledCreated = fst deletedAfter
    created' :: Timeline (WithOrigin SlotNo) TxIn
    created' = snd deletedAfter

-- |
-- Combine all changes before the given 'SlotNo'.
--
-- Using 'prune' will free up some space as old information
-- can be summarized and discarded.
pruneBefore :: SlotNo -> TimelineUTxO -> TimelineUTxO
pruneBefore newFinality old =
    TimelineUTxO
        (excluding (history old) prunedTxIns)
        (Haskell.Data.Maps.Timeline.difference (created old) prunedTxIns)
        spent1
        (boot old)
  where
    pruned :: (Set TxIn, Timeline SlotNo TxIn)
    pruned =
        Haskell.Data.Maps.Timeline.dropWhileAntitone
            (<= newFinality)
            (spent old)
    prunedTxIns :: Set TxIn
    prunedTxIns = fst pruned
    spent1 :: Timeline SlotNo TxIn
    spent1 = snd pruned

-- * Properties

-- $prop-insertDeltaUTxO-dropAfter-cancel
-- #p:prop-insertDeltaUTxO-dropAfter-cancel#
--
-- [prop-insertDeltaUTxO-dropAfter-cancel]:
--     Rolling backward will cancel rolling forward.
--     Bare version.
--
--     > @0 prop-insertDeltaUTxO-dropAfter-cancel
--     >   : ∀ (u : TimelineUTxO) (du : DeltaUTxO) (slot1 : Slot) (slot2 : SlotNo)
--     >   → (slot1 < WithOrigin.At slot2) ≡ True
--     >   → dropAfter slot1 (insertDeltaUTxO slot2 du u)
--     >     ≡ dropAfter slot1 u
