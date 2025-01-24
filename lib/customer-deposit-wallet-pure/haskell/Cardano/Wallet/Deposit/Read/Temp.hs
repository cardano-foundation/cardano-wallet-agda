module Cardano.Wallet.Deposit.Read.Temp where

import Cardano.Wallet.Read.Address (CompactAddr)
import Cardano.Wallet.Read.Tx (TxIn, TxOut)
import Prelude hiding (null, subtract)

-- |
-- Default type for addresses on the Cardano ledger.
--
-- Consider using 'CompactAddr' or 'Addr' directly if you want more control
-- over space and time usage.
--
-- NOTE: To be moved into "Cardano.Wallet.Read"
type Address = CompactAddr

-- |
-- Transaction body
--
-- NOTE: To be absorbed by "Cardano.Wallet.Write"
data TxBody = TxBodyC {inputs :: [TxIn], outputs :: [TxOut]}
