module Cardano.Wallet.Deposit.Pure.TxSummary where

import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Cardano.Wallet.Read.Chain (ChainPoint (GenesisPoint))
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx (Tx, TxId, getTxId)

data TxSummary = TxSummary
    { txSummarized :: TxId
    , txChainPoint :: ChainPoint
    , txTransfer :: ValueTransfer
    }

mkTxSummary :: IsEra era => Tx era -> ValueTransfer -> TxSummary
mkTxSummary =
    \tx transfer' -> TxSummary (getTxId tx) GenesisPoint transfer'
