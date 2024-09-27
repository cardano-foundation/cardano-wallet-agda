module Cardano.Wallet.Deposit.Pure.TxHistory.Core where

import Cardano.Wallet.Deposit.Pure.TxHistory.Type
    ( TxHistory (tip, txBlocks, txIds, txTransfers)
    )
import Cardano.Wallet.Deposit.Pure.TxSummary (TxSummary (TxSummaryC))
import Cardano.Wallet.Deposit.Pure.UTxO.Tx
    ( ResolvedTx
    , valueTransferFromResolvedTx
    )
import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Cardano.Wallet.Deposit.Read (Address)
import Cardano.Wallet.Read.Block (SlotNo)
import Cardano.Wallet.Read.Chain
    ( ChainPoint
    , Slot
    , WithOrigin (Origin)
    , slotFromChainPoint
    )
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx (TxId)
import Data.Set (Set)
import Haskell.Data.List (foldl')
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map
    ( empty
    , keysSet
    , lookup
    , mapMaybeWithKey
    , toAscList
    , unionWith
    , withoutKeys
    )
import qualified Haskell.Data.Maps.PairMap as PairMap
    ( PairMap
    , empty
    , insert
    , lookupA
    , lookupB
    , withoutKeysA
    )
import qualified Haskell.Data.Maps.Timeline as Timeline
    ( Timeline
    , deleteAfter
    , empty
    , getMapTime
    , insertMany
    , insertManyKeys
    , restrictRange
    )
import qualified Haskell.Data.Set as Set (fromList)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.TxHistory.Type
    ( TxHistory (..)
    )
import Data.Foldable
    ( toList
    )

-- |
-- The empty transaction history.
-- It starts at genesis and contains no transactions.
empty :: TxHistory
empty = TxHistory Timeline.empty Map.empty PairMap.empty Origin

-- |
-- 'getTip' records the slot up to which the transaction history
-- includes information from blocks. All blocks from genesis up to and
-- including this slot have been inspected for relevant transactions.
getTip :: TxHistory -> Slot
getTip = \r -> tip r

-- |
-- Get the transaction history for a single address.
getAddressHistory :: Address -> TxHistory -> Map TxId TxSummary
getAddressHistory address history = txSummaries
  where
    valueTransfers :: Map TxId ValueTransfer
    valueTransfers = PairMap.lookupB address (txTransfers history)
    makeTxSummary :: TxId -> ValueTransfer -> Maybe TxSummary
    makeTxSummary txid v =
        case Map.lookup txid (txBlocks history) of
            Nothing -> Nothing
            Just b -> Just (TxSummaryC txid b v)
    txSummaries :: Map TxId TxSummary
    txSummaries = Map.mapMaybeWithKey makeTxSummary valueTransfers

-- |
-- Get the total 'ValueTransfer' in a given slot range.
getValueTransfers
    :: (Slot, Slot) -> TxHistory -> Map Address ValueTransfer
getValueTransfers range history =
    foldl' (Map.unionWith (<>)) Map.empty txs2
  where
    txs1 :: Set TxId
    txs1 =
        Map.keysSet
            ( Timeline.getMapTime
                (Timeline.restrictRange range (txIds history))
            )
    txs2 :: [Map Address ValueTransfer]
    txs2 =
        map
            (\tx -> PairMap.lookupA tx (txTransfers history))
            (toList txs1)

-- |
-- Include the information contained in the block at 'SlotNo'
-- into the transaction history.
-- We expect that the block has already been digested into a list
-- of 'ResolvedTx'.
rollForward
    :: IsEra era
    => ChainPoint
    -> [(TxId, ResolvedTx era)]
    -> TxHistory
    -> TxHistory
rollForward newTip txs history =
    if newSlot <= getTip history
        then history
        else
            TxHistory
                (Timeline.insertMany newSlot txids (txIds history))
                (Timeline.insertManyKeys txids newTip (txBlocks history))
                (foldl' insertValueTransfer (txTransfers history) txs)
                newSlot
  where
    newSlot :: Slot
    newSlot = slotFromChainPoint newTip
    txids :: Set TxId
    txids = Set.fromList (map (\r -> fst r) txs)
    insertValueTransfer
        :: IsEra era1
        => PairMap.PairMap TxId Address ValueTransfer
        -> (TxId, ResolvedTx era1)
        -> PairMap.PairMap TxId Address ValueTransfer
    insertValueTransfer m0 (txid, tx) =
        foldl' (uncurry . fun) m0 (Map.toAscList mv)
      where
        mv :: Map Address ValueTransfer
        mv = valueTransferFromResolvedTx tx
        fun
            :: PairMap.PairMap TxId Address ValueTransfer
            -> Address
            -> ValueTransfer
            -> PairMap.PairMap TxId Address ValueTransfer
        fun = \m addr v -> PairMap.insert txid addr v m

-- |
-- Roll back the transaction history to the given 'Slot',
-- i.e. forget about all transaction that are strictly later than this slot.
rollBackward :: Slot -> TxHistory -> TxHistory
rollBackward new history =
    if new > getTip history
        then history
        else
            TxHistory
                keptTimeline
                (Map.withoutKeys (txBlocks history) deletedTxIds)
                (PairMap.withoutKeysA (txTransfers history) deletedTxIds)
                new
  where
    deleteAfterTxIds
        :: (Set TxId, Timeline.Timeline (WithOrigin SlotNo) TxId)
    deleteAfterTxIds = Timeline.deleteAfter new (txIds history)
    deletedTxIds :: Set TxId
    deletedTxIds = fst deleteAfterTxIds
    keptTimeline :: Timeline.Timeline (WithOrigin SlotNo) TxId
    keptTimeline = snd deleteAfterTxIds
