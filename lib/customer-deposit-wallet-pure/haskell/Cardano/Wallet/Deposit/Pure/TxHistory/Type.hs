module Cardano.Wallet.Deposit.Pure.TxHistory.Type where

import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Cardano.Wallet.Deposit.Read (Address, Slot, TxId)
import Haskell.Data.InverseMap (InverseMap)
import Haskell.Data.Map (Map)
import Haskell.Data.Maps.PairMap (PairMap)

data TxHistory = TxHistory{txSlotsByTxId :: Map TxId Slot,
                           txSlotsBySlot :: InverseMap TxId Slot,
                           txTransfers :: PairMap TxId Address ValueTransfer, tip :: Slot}

