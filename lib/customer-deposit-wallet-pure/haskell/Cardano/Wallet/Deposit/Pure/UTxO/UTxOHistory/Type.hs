{-# LANGUAGE StandaloneDeriving #-}
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import Cardano.Wallet.Deposit.Read (Slot, SlotNo, TxIn)
import Haskell.Data.InverseMap (InverseMap)
import Haskell.Data.Map (Map)

data Pruned = PrunedUpTo SlotNo
            | NotPruned

deriving instance Eq Pruned

deriving instance Show Pruned

data UTxOHistory = UTxOHistory{history :: UTxO,
                               creationSlots :: InverseMap TxIn Slot,
                               creationTxIns :: Map TxIn Slot,
                               spentSlots :: InverseMap TxIn SlotNo,
                               spentTxIns :: Map TxIn SlotNo, tip :: Slot, finality :: Pruned,
                               boot :: UTxO}

