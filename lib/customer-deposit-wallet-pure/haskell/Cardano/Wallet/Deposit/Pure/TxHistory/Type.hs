module Cardano.Wallet.Deposit.Pure.TxHistory.Type where

import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Cardano.Wallet.Deposit.Read (Address, Slot)
import Cardano.Wallet.Read.Tx (TxId)
import Haskell.Data.Maps.PairMap (PairMap)
import Haskell.Data.Maps.Timeline (Timeline)

data TxHistory = TxHistory
    { txIds :: Timeline Slot TxId
    , txTransfers :: PairMap TxId Address ValueTransfer
    , tip :: Slot
    }
