{-# LANGUAGE LambdaCase #-}
module Cardano.Wallet.Deposit.Pure.TxHistory.Core where

import Cardano.Wallet.Deposit.Pure.TxHistory.Type (TxHistory(tip, txIds, txTransfers))
import Cardano.Wallet.Deposit.Pure.UTxO.Tx (ResolvedTx, valueTransferFromResolvedTx)
import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Cardano.Wallet.Deposit.Read (Address, Slot, SlotNo, TxId, WithOrigin(At, Origin))
import Data.Set (Set)
import qualified Haskell.Data.ByteString (ByteString)
import Haskell.Data.List (foldl', sortOn)
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map (empty, keysSet, restrictKeys, toAscList, unionWith)
import qualified Haskell.Data.Maps.PairMap as PairMap (PairMap, empty, insert, lookupA, lookupB, withoutKeysA)
import qualified Haskell.Data.Maps.Timeline as Timeline (Timeline, deleteAfter, empty, getMapTime, insertMany, restrictRange)
import qualified Haskell.Data.Set as Set (fromList)
import Numeric.Natural (Natural)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.TxHistory.Type
    ( TxHistory (..)
    )
import Data.Foldable
    ( toList
    )

empty :: TxHistory
empty = TxHistory Timeline.empty PairMap.empty Origin

getTip :: TxHistory -> Slot
getTip = \ r -> tip r

getAddressHistory :: Address -> TxHistory -> [(Slot, TxId)]
getAddressHistory address history
  = sortOn (\ r -> fst r)
      (map
         (\case
              (x, y) -> (y, x))
         (Map.toAscList txs2))
  where
    txs1 :: Set TxId
    txs1 = Map.keysSet (PairMap.lookupB address (txTransfers history))
    txs2 :: Map TxId Slot
    txs2 = Map.restrictKeys (Timeline.getMapTime (txIds history)) txs1

getValueTransfers ::
                  (Slot, Slot) -> TxHistory -> Map Address ValueTransfer
getValueTransfers range history
  = foldl' (Map.unionWith (<>)) Map.empty txs2
  where
    txs1 :: Set TxId
    txs1
      = Map.keysSet
          (Timeline.getMapTime
             (Timeline.restrictRange range (txIds history)))
    txs2 :: [Map Address ValueTransfer]
    txs2
      = map (\ tx -> PairMap.lookupA tx (txTransfers history))
          (toList txs1)

rollForward ::
            SlotNo -> [(TxId, ResolvedTx)] -> TxHistory -> TxHistory
rollForward new txs history
  = if At new <= getTip history then history else
      TxHistory (Timeline.insertMany slot txids (txIds history))
        (foldl' insertValueTransfer (txTransfers history) txs)
        (At new)
  where
    slot :: WithOrigin Natural
    slot = At new
    txids :: Set TxId
    txids = Set.fromList (map (\ r -> fst r) txs)
    insertValueTransfer ::
                        PairMap.PairMap TxId Address ValueTransfer ->
                          (TxId, ResolvedTx) -> PairMap.PairMap TxId Address ValueTransfer
    insertValueTransfer m0 (txid, tx)
      = foldl' (uncurry . fun) m0 (Map.toAscList mv)
      where
        mv :: Map Address ValueTransfer
        mv = valueTransferFromResolvedTx tx
        fun ::
            PairMap.PairMap Haskell.Data.ByteString.ByteString Address
              ValueTransfer
              ->
              Address ->
                ValueTransfer ->
                  PairMap.PairMap Haskell.Data.ByteString.ByteString Address
                    ValueTransfer
        fun = \ m addr v -> PairMap.insert txid addr v m

rollBackward :: Slot -> TxHistory -> TxHistory
rollBackward new history
  = if new > getTip history then history else
      TxHistory keptTimeline
        (PairMap.withoutKeysA (txTransfers history) deletedTxIds)
        new
  where
    deleteAfterTxIds ::
                     (Set TxId, Timeline.Timeline (WithOrigin SlotNo) TxId)
    deleteAfterTxIds = Timeline.deleteAfter new (txIds history)
    deletedTxIds :: Set TxId
    deletedTxIds = fst deleteAfterTxIds
    keptTimeline :: Timeline.Timeline (WithOrigin SlotNo) TxId
    keptTimeline = snd deleteAfterTxIds

