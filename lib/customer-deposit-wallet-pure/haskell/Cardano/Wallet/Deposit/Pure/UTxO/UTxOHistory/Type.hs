{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import Cardano.Wallet.Deposit.Read (Slot)
import Cardano.Wallet.Read.Block (SlotNo)
import Cardano.Wallet.Read.Tx (TxIn)
import Haskell.Data.Maps.Timeline (Timeline)

data Pruned
    = PrunedUpTo SlotNo
    | NotPruned

deriving instance Eq Pruned

deriving instance Show Pruned

data UTxOHistory = UTxOHistory
    { history :: UTxO
    , created :: Timeline Slot TxIn
    , spent :: Timeline SlotNo TxIn
    , tip :: Slot
    , finality :: Pruned
    , boot :: UTxO
    }
