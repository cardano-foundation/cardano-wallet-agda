module Cardano.Write.Tx.Balance where

import Cardano.Wallet.Deposit.Pure.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO as UTxO (balance)
import Cardano.Wallet.Deposit.Read (Address, TxBody(TxBodyC), TxIn, TxOut(TxOutC, value), Value, exceeds, minus)
import qualified Haskell.Data.Map as Map (toAscList)

data PartialTx = PartialTxC{outputs :: [TxOut]}

totalOut :: PartialTx -> Value
totalOut = mconcat . map (\ r -> value r) . \ r -> outputs r

type ChangeAddressGen c = c -> (Address, c)

secondCons :: b -> (a, [b]) -> (a, [b])
secondCons y (x, ys) = (x, y : ys)

coinSelectionGreedy :: Value -> [(TxIn, TxOut)] -> (Value, [TxIn])
coinSelectionGreedy v [] = (mempty, [])
coinSelectionGreedy v ((txin, txout) : xs)
  = if exceeds v (value txout) then
      secondCons txin $ coinSelectionGreedy (minus v (value txout)) xs
      else (minus (value txout) v, [])

balanceTransaction ::
                   UTxO -> ChangeAddressGen c -> c -> PartialTx -> Maybe TxBody
balanceTransaction utxo newAddress c0 partialTx
  = if exceeds target (UTxO.balance utxo) then Nothing else
      Just $
        TxBodyC (snd (coinSelectionGreedy target (Map.toAscList utxo)))
          (TxOutC (fst (newAddress c0))
             (fst (coinSelectionGreedy target (Map.toAscList utxo)))
             : outputs partialTx)
  where
    target :: Value
    target = totalOut partialTx

