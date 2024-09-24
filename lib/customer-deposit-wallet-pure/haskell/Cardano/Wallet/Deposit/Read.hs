module Cardano.Wallet.Deposit.Read where

import Cardano.Wallet.Read.Address (CompactAddr)
import Cardano.Wallet.Read.Block (Block)
import Cardano.Wallet.Read.Chain (ChainPoint, getChainPoint)
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx (Tx, TxIn, TxOut)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read.Value
    ( Value
    )

type Addr = CompactAddr

type Address = Addr

data TxBody = TxBodyC {inputs :: [TxIn], outputs :: [TxOut]}

getEraTransactions :: IsEra era => Block era -> [Tx era]
getEraTransactions block = []

chainPointFromBlock :: IsEra era => Block era -> ChainPoint
chainPointFromBlock = getChainPoint
