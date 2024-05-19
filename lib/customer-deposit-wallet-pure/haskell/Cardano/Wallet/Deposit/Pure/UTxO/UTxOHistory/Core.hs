{-# LANGUAGE LambdaCase #-}
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core where

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO (DeltaUTxO(excluded, received))
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO, dom, excluding)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (union)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type (Pruned(NotPruned, PrunedUpTo), UTxOHistory(boot, creationSlots, creationTxIns, finality, history, spentSlots, spentTxIns, tip))
import Cardano.Wallet.Deposit.Read (Slot, SlotNo, TxIn, WithOrigin(At, Origin))
import Data.Set (Set)
import qualified Haskell.Data.InverseMap as InverseMap (difference, empty, insertManyKeys)
import Haskell.Data.List (foldl')
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map (dropWhileAntitone, empty, insert, restrictKeys, spanAntitone, takeWhileAntitone, withoutKeys)
import Haskell.Data.Maybe (fromMaybe)
import qualified Haskell.Data.Set as Set (difference, intersection)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (..)
    )

guard :: Bool -> Maybe ()
guard True = Just ()
guard False = Nothing

fold :: (Foldable t, Monoid m) => t m -> m
fold = foldMap id

insertManyKeys ::
                 (Ord key, Ord v) => Set key -> v -> Map key v -> Map key v
insertManyKeys keys v m0
  = foldl' (\ m key -> Map.insert key v m) m0 keys

empty :: UTxO -> UTxOHistory
empty utxo
  = UTxOHistory utxo
      (InverseMap.insertManyKeys (dom utxo) Origin InverseMap.empty)
      (insertManyKeys (dom utxo) Origin Map.empty)
      Map.empty
      Map.empty
      Origin
      NotPruned
      utxo

getUTxO :: UTxOHistory -> UTxO
getUTxO us = excluding (history us) (fold (spentSlots us))

getTip :: UTxOHistory -> Slot
getTip = \ r -> tip r

getFinality :: UTxOHistory -> Pruned
getFinality = \ r -> finality r

getSpent :: UTxOHistory -> Map TxIn SlotNo
getSpent = \ r -> spentTxIns r

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
         (InverseMap.insertManyKeys receivedTxIns (At newTip)
            (creationSlots noop))
         (insertManyKeys receivedTxIns (At newTip) (creationTxIns noop))
         (InverseMap.insertManyKeys excludedTxIns newTip (spentSlots noop))
         (insertManyKeys excludedTxIns newTip (spentTxIns noop))
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
          (fold (spentSlots noop))

rollback :: Slot -> UTxOHistory -> UTxOHistory
rollback newTip noop
  = constrainingRollback noop noop newTip
      (\case
           Just newTip' -> UTxOHistory
                             (excluding (history noop)
                                (fold (snd (Map.spanAntitone (<= newTip') (creationSlots noop)))))
                             (fst (Map.spanAntitone (<= newTip') (creationSlots noop)))
                             (Map.withoutKeys (creationTxIns noop)
                                (fold (snd (Map.spanAntitone (<= newTip') (creationSlots noop)))))
                             (case newTip' of
                                  Origin -> Map.empty
                                  At slot'' -> Map.takeWhileAntitone (<= slot'') (spentSlots noop))
                             (Map.withoutKeys (spentTxIns noop)
                                (fold
                                   (case newTip' of
                                        Origin -> spentSlots noop
                                        At slot'' -> Map.dropWhileAntitone (<= slot'')
                                                       (spentSlots noop))))
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
             (fold
                (fst (Map.spanAntitone (<= newFinality') (spentSlots noop)))))
          (InverseMap.difference (creationSlots noop)
             (Map.restrictKeys (creationTxIns noop)
                (fold
                   (fst (Map.spanAntitone (<= newFinality') (spentSlots noop))))))
          (Map.withoutKeys (creationTxIns noop)
             (fold
                (fst (Map.spanAntitone (<= newFinality') (spentSlots noop)))))
          (snd (Map.spanAntitone (<= newFinality') (spentSlots noop)))
          (Map.withoutKeys (spentTxIns noop)
             (fold
                (fst (Map.spanAntitone (<= newFinality') (spentSlots noop)))))
          (tip noop)
          (PrunedUpTo newFinality')
          (boot noop)
