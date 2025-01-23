{-# LANGUAGE StrictData #-}

module Cardano.Wallet.Deposit.Pure.TxHistory.Type where

import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer (ValueTransfer)
import Cardano.Wallet.Deposit.Read.Temp (Address)
import Data.Maps.PairMap (PairMap)
import Data.Maps.Timeline (Timeline)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read
    ( ChainPoint (..)
    , Slot
    , TxId
    )
import Data.Map (Map)

-- |
-- 'TxHistory'.
--
-- History of the transactions to and from the Deposit Wallet.
-- Information includes:
--
-- * Slot of each transaction
-- * Value transfer for each transaction, indexed by address
--
-- NOTE: This is an abstract data type,
-- its internals are only exported for technical reasons.
data TxHistory = TxHistory
    { txIds :: Timeline Slot TxId
    , txBlocks :: Map TxId ChainPoint
    , txTransfers :: PairMap TxId Address ValueTransfer
    , tip :: Slot
    }
