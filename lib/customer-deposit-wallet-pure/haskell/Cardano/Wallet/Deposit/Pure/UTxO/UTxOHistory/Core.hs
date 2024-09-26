module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core where

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

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (..)
    )

guard :: Bool -> Maybe ()
guard True = Just ()
guard False = Nothing

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
-- Returns the UTxO.
getUTxO :: UTxOHistory -> UTxO
getUTxO us =
    excluding
        (history us)
        (Map.keysSet (Timeline.getMapTime (spent us)))

-- |
-- Returns the 'RollbackWindow' slot.
getRollbackWindow
    :: UTxOHistory -> RollbackWindow.RollbackWindow Slot
getRollbackWindow x = window x

-- |
-- Returns the spent TxIns that can be rolled back.
getSpent :: UTxOHistory -> Map TxIn SlotNo
getSpent = Timeline.getMapTime . \r -> spent r

data DeltaUTxOHistory
    = AppendBlock SlotNo DeltaUTxO
    | Rollback Slot
    | Prune SlotNo

appendBlock :: SlotNo -> DeltaUTxO -> UTxOHistory -> UTxOHistory
appendBlock newTip delta old =
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

rollback :: Slot -> UTxOHistory -> UTxOHistory
rollback newTip old =
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
