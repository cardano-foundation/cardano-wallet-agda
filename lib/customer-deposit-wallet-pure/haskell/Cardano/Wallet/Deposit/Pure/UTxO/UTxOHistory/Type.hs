module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

import Cardano.Wallet.Deposit.Pure.RollbackWindow (RollbackWindow)
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import Cardano.Wallet.Read.Block (SlotNo)
import Cardano.Wallet.Read.Chain (Slot)
import Cardano.Wallet.Read.Tx (TxIn)
import Haskell.Data.Maps.Timeline (Timeline)
import Prelude hiding (null, subtract)

-- |
-- 'UTxOHistory' represents a history of a UTxO set that can be
-- rolled back (up to the 'finality' point).
--
-- NOTE: This is an abstract data type,
-- its internals are only exported for technical reasons.
data UTxOHistory = UTxOHistory
    { history :: UTxO
    , created :: Timeline Slot TxIn
    , spent :: Timeline SlotNo TxIn
    , window :: RollbackWindow Slot
    , boot :: UTxO
    }
