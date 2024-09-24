module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

import Cardano.Wallet.Deposit.Pure.RollbackWindow (RollbackWindow)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import Cardano.Wallet.Read.Block (SlotNo)
import Cardano.Wallet.Read.Chain (Slot)
import Cardano.Wallet.Read.Tx (TxIn)
import Haskell.Data.Maps.Timeline (Timeline)

data UTxOHistory = UTxOHistory
    { history :: UTxO
    , created :: Timeline Slot TxIn
    , spent :: Timeline SlotNo TxIn
    , window :: RollbackWindow Slot
    , boot :: UTxO
    }
