module Cardano.Wallet.Deposit.Read.Temp where

import Cardano.Wallet.Read.Address (CompactAddr)
import Cardano.Wallet.Read.Tx (TxIn, TxOut)

type Addr = CompactAddr

type Address = Addr

data TxBody = TxBodyC {inputs :: [TxIn], outputs :: [TxOut]}
