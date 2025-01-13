{-# LANGUAGE StrictData #-}

module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core
    ( -- * UTxOHistory
      UTxOHistory (..)
    , fromOrigin
    , getUTxO
    , getRollbackWindow
    , getTip

      -- * Operations
    , DeltaUTxOHistory (..)
    , applyDeltaUTxOHistory
    , rollForward
      -- $prop-rollForward-present
    , rollBackward
      -- $prop-rollBackward-tip
      -- $prop-rollBackward-future
      -- $prop-rollBackward-rollForward-cancel
      -- $prop-rollBackward-tip-rollForward
    , prune

      -- * Internal
    , getSpent
    )
where

import Cardano.Wallet.Deposit.Pure.RollbackWindow (RollbackWindow (tip))
import qualified Cardano.Wallet.Deposit.Pure.RollbackWindow
    ( MaybeRollback (Future, Past, Present)
    , prune
    , rollBackward
    , rollForward
    , singleton
    )
import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    ( DeltaUTxO (excluded, received)
    )
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO, dom, excluding)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (union)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (boot, created, history, spent, window)
    )
import Cardano.Wallet.Read.Block (SlotNo)
import Cardano.Wallet.Read.Chain (Slot, WithOrigin (At, Origin))
import Cardano.Wallet.Read.Tx (TxIn)
import Data.Set (Set)
import Haskell.Data.Map.Def (Map)
import qualified Haskell.Data.Maps.Timeline as Timeline
    ( Timeline
    , deleteAfter
    , difference
    , dropAfter
    , dropWhileAntitone
    , empty
    , getMapTime
    , insertMany
    , items
    )
import qualified Haskell.Data.Set.Def as Set (difference, intersection)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (..)
    )

-- |
-- A 'UTxOHistory' whose tip is at 'Origin'
-- with an initial 'UTxO'.
fromOrigin :: UTxO -> UTxOHistory
fromOrigin utxo =
    UTxOHistory
        utxo
        (Timeline.insertMany Origin (dom utxo) Timeline.empty)
        Timeline.empty
        (Cardano.Wallet.Deposit.Pure.RollbackWindow.singleton Origin)
        utxo

-- |
-- UTxO at the tip of history.
getUTxO :: UTxOHistory -> UTxO
getUTxO us = excluding (history us) (Timeline.items (spent us))

-- |
-- 'RollbackWindow' within which we can roll back.
--
-- The tip of the history is also the upper end of this window.
-- The UTxO history includes information from all blocks
-- between genesis and the tip, and including the block at the tip.
getRollbackWindow :: UTxOHistory -> RollbackWindow Slot
getRollbackWindow x = window x

-- |
-- Tip of the 'UTxOHistory'.
getTip :: UTxOHistory -> Slot
getTip = (\r -> tip r) . getRollbackWindow

-- |
-- The spent 'TxIn's that can be rolled back.
--
-- (Internal, exported for specification.)
getSpent :: UTxOHistory -> Map TxIn SlotNo
getSpent = Timeline.getMapTime . \r -> spent r

-- |
-- Representation of a change (delta) to a 'UTxOHistory'.
data DeltaUTxOHistory
    = AppendBlock SlotNo DeltaUTxO
    | Rollback Slot
    | Prune SlotNo

-- |
-- (Internal, exported for technical reasons.)
--
-- Roll forward under the assumption that we are moving to the future.
rollForwardBare
    :: SlotNo -> DeltaUTxO -> UTxOHistory -> UTxOHistory
rollForwardBare newTip delta old =
    UTxOHistory
        (UTxO.union (history old) (received delta))
        (Timeline.insertMany (At newTip) receivedTxIns (created old))
        (Timeline.insertMany newTip excludedTxIns (spent old))
        (window old)
        (boot old)
  where
    receivedTxIns :: Set TxIn
    receivedTxIns =
        Set.difference (dom (received delta)) (dom (history old))
    excludedTxIns :: Set TxIn
    excludedTxIns =
        Set.difference
            (Set.intersection (excluded delta) (dom (history old)))
            (Timeline.items (spent old))

-- |
-- (Internal, exported for technical reasons.)
rollForwardCases
    :: SlotNo
    -> DeltaUTxO
    -> UTxOHistory
    -> Maybe (RollbackWindow Slot)
    -> UTxOHistory
rollForwardCases newTip delta old Nothing = old
rollForwardCases newTip delta old (Just window') =
    UTxOHistory
        (history new')
        (created new')
        (spent new')
        window'
        (boot new')
  where
    new' :: UTxOHistory
    new' = rollForwardBare newTip delta old

-- |
-- Include the information contained in the block at 'SlotNo'
-- into the 'UTxOHistory'.
-- We expect that the block has already been digested into a single 'DeltaUTxO'.
rollForward :: SlotNo -> DeltaUTxO -> UTxOHistory -> UTxOHistory
rollForward newTip delta old =
    rollForwardCases
        newTip
        delta
        old
        ( Cardano.Wallet.Deposit.Pure.RollbackWindow.rollForward
            (At newTip)
            (window old)
        )

-- |
-- (Internal, exported for technical reasons.)
rollBackwardBareSpent
    :: Slot
    -> Timeline.Timeline SlotNo TxIn
    -> Timeline.Timeline SlotNo TxIn
rollBackwardBareSpent Origin spents = Timeline.empty
rollBackwardBareSpent (At slot) spents =
    Timeline.dropAfter slot spents

-- |
-- (Internal, exported for technical reasons.)
--
-- Roll backwards under the assumption that we are moving to the past.
rollBackwardBare :: Slot -> UTxOHistory -> UTxOHistory
rollBackwardBare newTip old =
    UTxOHistory
        (excluding (history old) rolledCreated)
        created'
        (rollBackwardBareSpent newTip (spent old))
        (window old)
        (boot old)
  where
    deletedAfter
        :: (Set TxIn, Timeline.Timeline (WithOrigin SlotNo) TxIn)
    deletedAfter = Timeline.deleteAfter newTip (created old)
    rolledCreated :: Set TxIn
    rolledCreated = fst deletedAfter
    created' :: Timeline.Timeline (WithOrigin SlotNo) TxIn
    created' = snd deletedAfter

-- |
-- (Internal, exported for technical reasons.)
rollBackwardCases
    :: Slot
    -> UTxOHistory
    -> Cardano.Wallet.Deposit.Pure.RollbackWindow.MaybeRollback
        (RollbackWindow Slot)
    -> UTxOHistory
rollBackwardCases
    newTip
    old
    Cardano.Wallet.Deposit.Pure.RollbackWindow.Future = old
rollBackwardCases
    newTip
    old
    Cardano.Wallet.Deposit.Pure.RollbackWindow.Past =
        fromOrigin (boot old)
rollBackwardCases
    newTip
    old
    (Cardano.Wallet.Deposit.Pure.RollbackWindow.Present window') =
        UTxOHistory
            (history new')
            (created new')
            (spent new')
            window'
            (boot new')
      where
        new' :: UTxOHistory
        new' = rollBackwardBare newTip old

-- |
-- Roll back the 'UTxOHistory' to the given 'Slot',
-- i.e. forget about all blocks that are strictly later than this slot.
rollBackward :: Slot -> UTxOHistory -> UTxOHistory
rollBackward newTip old =
    rollBackwardCases
        newTip
        old
        ( Cardano.Wallet.Deposit.Pure.RollbackWindow.rollBackward
            newTip
            (window old)
        )

-- |
-- Remove the ability to 'rollback' before the given 'SlotNo',
-- but rolling back to genesis is always possible.
--
-- Using 'prune' will free up some space as old information
-- can be summarized and discarded.
prune :: SlotNo -> UTxOHistory -> UTxOHistory
prune newFinality old =
    case Cardano.Wallet.Deposit.Pure.RollbackWindow.prune
        (At newFinality)
        (window old) of
        Nothing -> old
        Just window' ->
            UTxOHistory
                ( excluding
                    (history old)
                    (fst (Timeline.dropWhileAntitone (<= newFinality) (spent old)))
                )
                ( Timeline.difference
                    (created old)
                    (fst (Timeline.dropWhileAntitone (<= newFinality) (spent old)))
                )
                (snd (Timeline.dropWhileAntitone (<= newFinality) (spent old)))
                window'
                (boot old)

-- |
-- How to apply a DeltaUTxOHistory to a UTxOHistory
applyDeltaUTxOHistory
    :: DeltaUTxOHistory -> UTxOHistory -> UTxOHistory
applyDeltaUTxOHistory (AppendBlock newTip delta) =
    rollForward newTip delta
applyDeltaUTxOHistory (Rollback newTip) = rollBackward newTip
applyDeltaUTxOHistory (Prune newFinality) = prune newFinality

-- * Properties

-- $prop-rollBackward-future
-- #p:prop-rollBackward-future#
--
-- [prop-rollBackward-future]:
--     Rolling backward to the future does nothing.
--
--     > prop-rollBackward-future
--     >   : ∀ (u : UTxOHistory) (slot : Slot)
--     >   → (getTip u <= slot) ≡ True
--     >   → rollBackward slot u ≡ u

-- $prop-rollBackward-rollForward-cancel
-- #p:prop-rollBackward-rollForward-cancel#
--
-- [prop-rollBackward-rollForward-cancel]:
--     /Essential property:/
--     Rolling backward will cancel rolling forward.
--
--     > @0 prop-rollBackward-rollForward-cancel
--     >   : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot1 : Slot) (slot2 : SlotNo)
--     >   → (slot1 < WithOrigin.At slot2) ≡ True
--     >   → rollBackward slot1 (rollForward slot2 du u)
--     >     ≡ rollBackward slot1 u

-- $prop-rollBackward-tip
-- #p:prop-rollBackward-tip#
--
-- [prop-rollBackward-tip]:
--     Rolling backward to the tip does nothing, as we are already at the tip.
--     Special case of __prop-rollBackward-future__.
--
--     > prop-rollBackward-tip
--     >   : ∀ (u : UTxOHistory)
--     >   → rollBackward (getTip u) u ≡ u

-- $prop-rollBackward-tip-rollForward
-- #p:prop-rollBackward-tip-rollForward#
--
-- [prop-rollBackward-tip-rollForward]:
--     Rolling backward after a 'rollForward' will restore the original state.
--
--     > @0 prop-rollBackward-tip-rollForward
--     >   : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot : SlotNo)
--     >   → rollBackward (getTip u) (rollForward slot du u) ≡ u

-- $prop-rollForward-present
-- #p:prop-rollForward-present#
--
-- [prop-rollForward-present]:
--     Rolling forward to the tip or before the tip does nothing.
--
--     > @0 prop-rollForward-present
--     >   : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot : SlotNo)
--     >   → (WithOrigin.At slot <= getTip u) ≡ True
--     >   → rollForward slot du u ≡ u
