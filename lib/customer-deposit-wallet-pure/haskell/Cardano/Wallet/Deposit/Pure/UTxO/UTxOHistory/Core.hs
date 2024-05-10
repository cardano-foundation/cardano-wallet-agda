{-# LANGUAGE LambdaCase #-}
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core where

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO (DeltaUTxO(excluded, received))
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO, dom, excluding)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (union)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type (Pruned(NotPruned, PrunedUpTo), UTxOHistory(boot, creationSlots, creationTxIns, finality, history, spentSlots, spentTxIns, tip))
import Cardano.Wallet.Deposit.Read (Slot, SlotNo, TxIn, WithOrigin(At, Origin))
import Data.Set (Set)
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map (dropWhileAntitone, empty, fromList, insert, restrictKeys, singleton, spanAntitone, takeWhileAntitone, toAscList, update, withoutKeys)
import Haskell.Data.Maybe (fromMaybe)
import qualified Haskell.Data.Set as Set (delete, difference, intersection, null, toAscList)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (..)
    )

guard :: Bool -> Maybe ()
guard True = Just ()
guard False = Nothing

foldl' :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl' = foldl

fold :: (Foldable t, Monoid m) => t m -> m
fold = foldMap id

insertNonEmpty ::
                 (Ord key, Ord v) =>
                 key -> Set v -> Map key (Set v) -> Map key (Set v)
insertNonEmpty key x = if Set.null x then id else Map.insert key x

reverseMapOfSets ::
                   (Ord key, Ord v) => Map key (Set v) -> Map v key
reverseMapOfSets m
  = Map.fromList $
      do (k, vs) <- Map.toAscList m
         v <- Set.toAscList vs
         pure (v, k)

insertNonEmptyReversedMap ::
                            (Ord key, Ord v) => key -> Set v -> Map v key -> Map v key
insertNonEmptyReversedMap key vs m0
  = foldl' (\ m v -> Map.insert v key m) m0 vs

deleteFromSet :: Ord v => v -> Set v -> Maybe (Set v)
deleteFromSet x vs
  = if Set.null (Set.delete x vs) then Nothing else
      Just (Set.delete x vs)

deleteFromMap ::
                (Ord v, Ord key) => (v, key) -> Map key (Set v) -> Map key (Set v)
deleteFromMap (x, key) = Map.update (deleteFromSet x) key

differenceReversedMap ::
                        (Ord v, Ord key) => Map key (Set v) -> Map v key -> Map key (Set v)
differenceReversedMap whole part
  = foldl' (flip deleteFromMap) whole $ Map.toAscList part

empty :: UTxO -> UTxOHistory
empty utxo
  = UTxOHistory utxo creationSlots' (reverseMapOfSets creationSlots')
      Map.empty
      Map.empty
      Origin
      NotPruned
      utxo
  where
    creationSlots' :: Map (WithOrigin SlotNo) (Set TxIn)
    creationSlots' = Map.singleton Origin $ dom utxo

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
         (insertNonEmpty (At newTip) receivedTxIns (creationSlots noop))
         (insertNonEmptyReversedMap (At newTip) receivedTxIns
            (creationTxIns noop))
         (insertNonEmpty newTip excludedTxIns (spentSlots noop))
         (insertNonEmptyReversedMap newTip excludedTxIns (spentTxIns noop))
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
          (differenceReversedMap (creationSlots noop)
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

