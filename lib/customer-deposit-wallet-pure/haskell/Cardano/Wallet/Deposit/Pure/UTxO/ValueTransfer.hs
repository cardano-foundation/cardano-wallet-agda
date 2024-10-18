{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer where

import Cardano.Wallet.Read.Value (Value)
import Prelude hiding (null, subtract)

-- |
-- Records a transfer of 'Value'
-- — some 'Value' is spent, while other 'Value' is received.
data ValueTransfer = ValueTransferC
    { spent :: Value
    , received :: Value
    }

deriving instance Eq ValueTransfer

deriving instance Show ValueTransfer

-- |
-- Record spending a given 'Value'.
fromSpent :: Value -> ValueTransfer
fromSpent = \value -> ValueTransferC value mempty

-- |
-- Record receiving a given 'Value'.
fromReceived :: Value -> ValueTransfer
fromReceived = \value -> ValueTransferC mempty value

instance Semigroup ValueTransfer where
    (<>) =
        \v1 v2 ->
            ValueTransferC (spent v1 <> spent v2) (received v1 <> received v2)

instance Monoid ValueTransfer where
    mempty = ValueTransferC mempty mempty

-- * Properties

-- $prop-ValueTansfer-<>-comm
-- #prop-ValueTansfer-<>-comm#
--
-- [prop-ValueTansfer-<>-comm]:
--
--     'ValueTransfer' is a commutative semigroup.
--
--     @
--     prop-ValueTansfer-<>-comm
--       : ∀ (x y : ValueTransfer)
--       → x <> y ≡ y <> x
--     @
