module Cardano.Wallet.Deposit.Pure.TxSummary where

import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Cardano.Wallet.Deposit.Read (ChainPoint(GenesisPoint), Tx(txid), TxId)

data TxSummary = TxSummary{summarizedTx :: TxId,
                           point :: ChainPoint, transfer :: ValueTransfer}

mkTxSummary :: Tx -> ValueTransfer -> TxSummary
mkTxSummary
  = \ tx transfer' -> TxSummary (txid tx) GenesisPoint transfer'

