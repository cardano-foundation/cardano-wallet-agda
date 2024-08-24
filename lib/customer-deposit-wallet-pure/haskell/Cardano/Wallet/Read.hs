module Cardano.Wallet.Read
    ( module Cardano.Wallet.Read.Block
    , module Cardano.Wallet.Read.Chain
    , module Cardano.Wallet.Read.Eras
    , module Cardano.Wallet.Read.Value
    , Tx
    , getEraTransactions
    ) where

import Cardano.Wallet.Read.Block
import Cardano.Wallet.Read.Chain
import Cardano.Wallet.Read.Eras
import Cardano.Wallet.Read.Value

data Tx = Tx

getEraTransactions :: forall era. IsEra era => Block era -> [Tx]
getEraTransactions = undefined
