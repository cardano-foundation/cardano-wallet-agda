{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Deposit.Pure.TxSummary where

import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read
    ( ChainPoint (..)
    , IsEra
    , Tx
    , TxId
    , getTxId
    )

-- |
-- A 'TxSummary' summarizes a transaction.
--
-- Note: Haddock may be broken. The fields of this record
-- refer to types from "Cardano.Wallet.Read".
data TxSummary = TxSummaryC
    { txSummarized :: TxId
    , txChainPoint :: ChainPoint
    , txTransfer :: ValueTransfer
    }

deriving instance Eq TxSummary

deriving instance Show TxSummary

-- |
-- Create a 'TxSummary' from a transaction.
--
-- FIXME: This is a mock summary for now!
mkTxSummary :: IsEra era => Tx era -> ValueTransfer -> TxSummary
mkTxSummary =
    \tx transfer' -> TxSummaryC (getTxId tx) GenesisPoint transfer'
