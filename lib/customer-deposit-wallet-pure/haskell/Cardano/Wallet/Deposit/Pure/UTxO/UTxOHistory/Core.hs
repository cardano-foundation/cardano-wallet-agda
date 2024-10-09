module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core
    ( -- * UTxOHistory
      UTxOHistory
    , empty
    , getUTxO
    , getRollbackWindow

      -- * Changes
    , DeltaUTxOHistory (..)
    , applyDeltaUTxOHistory
    , appendBlock
    , rollback
    , prune

      -- * Internal
    , getSpent
    )
where

import qualified Cardano.Wallet.Deposit.Pure.RollbackWindow as RollbackWindow
    ( MaybeRollback (Future, Past, Present)
    , RollbackWindow (tip)
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
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map (keysSet)
import qualified Haskell.Data.Maps.Timeline as Timeline
    ( deleteAfter
    , difference
    , dropWhileAntitone
    , empty
    , getMapTime
    , insertMany
    , takeWhileAntitone
    )
import qualified Haskell.Data.Set as Set (difference, intersection)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (..)
    )

-- |
-- An empty UTxO history
empty :: UTxO -> UTxOHistory
empty utxo =
    UTxOHistory
        utxo
        (Timeline.insertMany Origin (dom utxo) Timeline.empty)
        Timeline.empty
        (RollbackWindow.singleton Origin)
        utxo

-- |
-- UTxO at the tip of history.
getUTxO :: UTxOHistory -> UTxO
getUTxO us =
    excluding
        (history us)
        (Map.keysSet (Timeline.getMapTime (spent us)))

-- |
-- 'RollbackWindow' within which we can roll back.
--
-- The tip of the history is also the upper end of this window.
-- The UTxO history includes information from all blocks
-- between genesis and the tip, and including the block at the tip.
getRollbackWindow
    :: UTxOHistory -> RollbackWindow.RollbackWindow Slot
getRollbackWindow x = window x

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
-- Include the information contained in the block at 'SlotNo'
-- into the 'UTxOHistory'.
-- We expect that the block has already been digested into a single 'DeltaUTxO'.
rollForward :: SlotNo -> DeltaUTxO -> UTxOHistory -> UTxOHistory
rollForward newTip delta old =
    case RollbackWindow.rollForward (At newTip) (window old) of
        Nothing -> old
        Just window' ->
            UTxOHistory
                (UTxO.union (history old) (received delta))
                (Timeline.insertMany (At newTip) receivedTxIns (created old))
                (Timeline.insertMany newTip excludedTxIns (spent old))
                window'
                (boot old)
  where
    receivedTxIns :: Set TxIn
    receivedTxIns =
        Set.difference (dom (received delta)) (dom (history old))
    excludedTxIns :: Set TxIn
    excludedTxIns =
        Set.difference
            (Set.intersection (excluded delta) (dom (history old)))
            (Map.keysSet (Timeline.getMapTime (spent old)))

-- |
-- Roll back the 'UTxOHistory' to the given 'Slot',
-- i.e. forget about all blocks that are strictly later than this slot.
rollBackward :: Slot -> UTxOHistory -> UTxOHistory
rollBackward newTip old =
    case RollbackWindow.rollBackward newTip (window old) of
        RollbackWindow.Future -> old
        RollbackWindow.Past -> empty (boot old)
        RollbackWindow.Present window' ->
            UTxOHistory
                ( excluding
                    (history old)
                    ( fst
                        ( Timeline.deleteAfter
                            (RollbackWindow.tip window')
                            (created old)
                        )
                    )
                )
                ( snd
                    ( Timeline.deleteAfter
                        (RollbackWindow.tip window')
                        (created old)
                    )
                )
                ( case RollbackWindow.tip window' of
                    Origin -> Timeline.empty
                    At slot'' ->
                        snd
                            ( Timeline.takeWhileAntitone
                                (<= slot'')
                                (spent old)
                            )
                )
                window'
                (boot old)

-- |
-- Remove the ability to 'rollback' before the given 'SlotNo',
-- but rolling back to genesis is always possible.
--
-- Using 'prune' will free up some space as old information
-- can be summarized and discarded.
prune :: SlotNo -> UTxOHistory -> UTxOHistory
prune newFinality old =
    case RollbackWindow.prune (At newFinality) (window old) of
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
    appendBlock newTip delta
applyDeltaUTxOHistory (Rollback newTip) = rollback newTip
applyDeltaUTxOHistory (Prune newFinality) = prune newFinality
