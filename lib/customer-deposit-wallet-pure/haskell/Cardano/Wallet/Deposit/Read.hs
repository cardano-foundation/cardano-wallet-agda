module Cardano.Wallet.Deposit.Read where

import Cardano.Wallet.Read.Address (CompactAddr)
import Cardano.Wallet.Read.Tx (TxIn, TxOut)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read.Value
    ( Value
    )

type Addr = CompactAddr

type Address = Addr

data TxBody = TxBodyC {inputs :: [TxIn], outputs :: [TxOut]}
