{-# LANGUAGE StandaloneDeriving #-}
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import Cardano.Wallet.Deposit.Read (Slot, SlotNo, TxIn)
import Data.Set (Set)
import Haskell.Data.Map (Map)

data Pruned = PrunedUpTo SlotNo
            | NotPruned

deriving instance Eq Pruned

deriving instance Show Pruned

data UTxOHistory = UTxOHistory{history :: UTxO,
                               creationSlots :: Map Slot (Set TxIn),
                               creationTxIns :: Map TxIn Slot,
                               spentSlots :: Map SlotNo (Set TxIn), spentTxIns :: Map TxIn SlotNo,
                               tip :: Slot, finality :: Pruned, boot :: UTxO}

