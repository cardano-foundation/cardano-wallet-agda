{-# LANGUAGE LambdaCase #-}
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core where

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO (DeltaUTxO(excluded, received))
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO, dom, excluding)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (union)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type (Pruned(NotPruned, PrunedUpTo), UTxOHistory(boot, created, finality, history, spent, tip))
import Cardano.Wallet.Deposit.Read (Slot, SlotNo, TxIn, WithOrigin(At, Origin))
import Data.Set (Set)
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map (keysSet)
import qualified Haskell.Data.Maps.Timeline as Timeline (deleteAfter, difference, dropWhileAntitone, empty, getMapTime, insertMany, takeWhileAntitone)
import Haskell.Data.Maybe (fromMaybe)
import qualified Haskell.Data.Set as Set (difference, intersection)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (..)
    )

guard :: Bool -> Maybe ()
guard True = Just ()
guard False = Nothing

empty :: UTxO -> UTxOHistory
empty utxo
  = UTxOHistory utxo
      (Timeline.insertMany Origin (dom utxo) Timeline.empty)
      Timeline.empty
      Origin
      NotPruned
      utxo

getUTxO :: UTxOHistory -> UTxO
getUTxO us
  = excluding (history us)
      (Map.keysSet (Timeline.getMapTime (spent us)))

getTip :: UTxOHistory -> Slot
getTip = \ r -> tip r

getFinality :: UTxOHistory -> Pruned
getFinality = \ r -> finality r

getSpent :: UTxOHistory -> Map TxIn SlotNo
getSpent = Timeline.getMapTime . \ r -> spent r

constrainingAppendBlock :: a -> UTxOHistory -> SlotNo -> a -> a
constrainingAppendBlock noop us newTip f
  = if At newTip <= tip us then noop else f

constrainingRollback ::
                     a -> UTxOHistory -> Slot -> (Maybe Slot -> a) -> a
constrainingRollback noop us newTip f
  = if newTip >= tip us then noop else
      f (case finality us of
             NotPruned -> Just newTip
             PrunedUpTo finality' -> if newTip >= At finality' then Just newTip
                                       else Nothing)

constrainingPrune ::
                  a -> UTxOHistory -> SlotNo -> (SlotNo -> a) -> a
constrainingPrune noop us newFinality f
  = fromMaybe noop $
      do case finality us of
             NotPruned -> pure ()
             PrunedUpTo finality' -> guard $ newFinality > finality'
         case tip us of
             Origin -> Nothing
             At tip' -> pure $ f $ min newFinality tip'

data DeltaUTxOHistory = AppendBlock SlotNo DeltaUTxO
                      | Rollback Slot
                      | Prune SlotNo

appendBlock :: SlotNo -> DeltaUTxO -> UTxOHistory -> UTxOHistory
appendBlock newTip delta noop
  = constrainingAppendBlock noop noop newTip
      (UTxOHistory (UTxO.union (history noop) (received delta))
         (Timeline.insertMany (At newTip) receivedTxIns (created noop))
         (Timeline.insertMany newTip excludedTxIns (spent noop))
         (At newTip)
         (finality noop)
         (boot noop))
  where
    receivedTxIns :: Set TxIn
    receivedTxIns
      = Set.difference (dom (received delta)) (dom (history noop))
    excludedTxIns :: Set TxIn
    excludedTxIns
      = Set.difference
          (Set.intersection (excluded delta) (dom (history noop)))
          (Map.keysSet (Timeline.getMapTime (spent noop)))

rollback :: Slot -> UTxOHistory -> UTxOHistory
rollback newTip noop
  = constrainingRollback noop noop newTip
      (\case
           Just newTip' -> UTxOHistory
                             (excluding (history noop)
                                (fst (Timeline.deleteAfter newTip' (created noop))))
                             (snd (Timeline.deleteAfter newTip' (created noop)))
                             (case newTip' of
                                  Origin -> Timeline.empty
                                  At slot'' -> snd
                                                 (Timeline.takeWhileAntitone (<= slot'')
                                                    (spent noop)))
                             newTip'
                             (finality noop)
                             (boot noop)
           Nothing -> empty (boot noop))

prune :: SlotNo -> UTxOHistory -> UTxOHistory
prune newFinality noop
  = constrainingPrune noop noop newFinality $
      \ newFinality' ->
        UTxOHistory
          (excluding (history noop)
             (fst (Timeline.dropWhileAntitone (<= newFinality') (spent noop))))
          (Timeline.difference (created noop)
             (fst (Timeline.dropWhileAntitone (<= newFinality') (spent noop))))
          (snd (Timeline.dropWhileAntitone (<= newFinality') (spent noop)))
          (tip noop)
          (PrunedUpTo newFinality')
          (boot noop)

