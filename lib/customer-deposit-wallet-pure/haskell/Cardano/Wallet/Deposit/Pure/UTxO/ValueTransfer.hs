module Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer where

import Cardano.Wallet.Deposit.Read (Value)

data ValueTransfer = ValueTransfer{spent :: Value,
                                   received :: Value}

fromSpent :: Value -> ValueTransfer
fromSpent = \ value -> ValueTransfer value mempty

fromReceived :: Value -> ValueTransfer
fromReceived = \ value -> ValueTransfer mempty value

instance Semigroup ValueTransfer where
    (<>)
      = \ v1 v2 ->
          ValueTransfer (spent v1 <> spent v2) (received v1 <> received v2)

instance Monoid ValueTransfer where
    mempty = ValueTransfer mempty mempty

