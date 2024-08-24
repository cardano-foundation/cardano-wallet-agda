module Cardano.Write.Tx.Balance where

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO (balance)
import Cardano.Wallet.Deposit.Read (Address, TxBody (TxBodyC))
import Cardano.Wallet.Read.Tx (TxIn, TxOut, getValue, mkBasicTxOut)
import Cardano.Wallet.Read.Value (Value, largerOrEqual, subtract)
import qualified Haskell.Data.Map as Map (toAscList)

import Prelude hiding (subtract)

data PartialTx = PartialTxC {outputs :: [TxOut]}

totalOut :: PartialTx -> Value
totalOut = mconcat . map getValue . \r -> outputs r

type ChangeAddressGen c = c -> (Address, c)

secondCons :: b -> (a, [b]) -> (a, [b])
secondCons y (x, ys) = (x, y : ys)

coinSelectionGreedy :: Value -> [(TxIn, TxOut)] -> (Value, [TxIn])
coinSelectionGreedy v [] = (mempty, [])
coinSelectionGreedy v ((txin, txout) : xs) =
    if largerOrEqual v (getValue txout)
        then
            secondCons txin
                $ coinSelectionGreedy (subtract v (getValue txout)) xs
        else (subtract (getValue txout) v, [])

balanceTransaction
    :: UTxO -> ChangeAddressGen c -> c -> PartialTx -> Maybe TxBody
balanceTransaction utxo newAddress c0 partialTx =
    if largerOrEqual target (UTxO.balance utxo)
        then Nothing
        else
            Just
                $ TxBodyC
                    (snd (coinSelectionGreedy target (Map.toAscList utxo)))
                    ( mkBasicTxOut
                        (fst (newAddress c0))
                        (fst (coinSelectionGreedy target (Map.toAscList utxo)))
                        : outputs partialTx
                    )
  where
    target :: Value
    target = totalOut partialTx
