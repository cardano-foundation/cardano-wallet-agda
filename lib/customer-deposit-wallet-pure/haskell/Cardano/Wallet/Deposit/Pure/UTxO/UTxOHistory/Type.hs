module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

import Cardano.Wallet.Deposit.Pure.RollbackWindow (RollbackWindow)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import Cardano.Wallet.Read.Block (SlotNo)
import Cardano.Wallet.Read.Chain (Slot)
import Cardano.Wallet.Read.Tx (TxIn)
import Haskell.Data.Maps.Timeline (Timeline)

-- |
-- UTxO history.
-- Abstract history of the UTxO. We keep track of the creation
-- and spending of slot of each TxIn.
-- This allows us to rollback to a given slot
-- and prune the history to a given slot.
data UTxOHistory = UTxOHistory
    { history :: UTxO
    , created :: Timeline Slot TxIn
    , spent :: Timeline SlotNo TxIn
    , window :: RollbackWindow Slot
    , boot :: UTxO
    }
