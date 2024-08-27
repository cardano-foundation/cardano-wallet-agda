{- |
Copyright: © 2022 IOHK, 2024 Cardano Foundation
License: Apache-2.0

The 'Tx' type represents transactions as they are read from the mainnet ledger.
It is compatible with the era-specific index types from @cardano-ledger@.
-}
module Cardano.Wallet.Read.Tx
    ( Tx (..)
    , TxT

    , TxId
    , getTxId

    , TxIn
    , getInputs

    , TxOut
    , getCompactAddr
    , getValue
    , mkBasicTxOut
    , utxoFromEraTx
    ) where

import Cardano.Wallet.Read.Tx.Inputs
    ( getInputs
    )
import Cardano.Read.Ledger.Tx.Tx
    ( Tx (..)
    , TxT
    )
import Cardano.Wallet.Read.Tx.TxId
    ( TxId
    , getTxId
    )
import Cardano.Wallet.Read.Tx.TxIn
    ( TxIn
    )
import Cardano.Wallet.Read.Tx.TxOut
    ( TxOut
    , getCompactAddr
    , getValue
    , mkBasicTxOut
    , utxoFromEraTx
    )
