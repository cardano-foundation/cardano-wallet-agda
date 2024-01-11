module Cardano.Wallet.Deposit.Pure.Balance where

import Cardano.Wallet.Deposit.Pure.DeltaUTxO (DeltaUTxO)
import qualified Cardano.Wallet.Deposit.Pure.DeltaUTxO (excludingD, null, receiveD)
import Cardano.Wallet.Deposit.Pure.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO as UTxO (filterByAddress, null)
import Cardano.Wallet.Deposit.Read (Tx(inputs, outputs, txid))
import qualified Cardano.Wallet.Deposit.Read as Read (Addr, TxIn, TxOut)
import Data.Set (Set)
import qualified Haskell.Data.ByteString (ByteString)
import qualified Haskell.Data.Map as Map (fromList)
import qualified Haskell.Data.Set as Set (fromList)

spendTxD :: Tx -> UTxO -> (DeltaUTxO, UTxO)
spendTxD tx u
  = Cardano.Wallet.Deposit.Pure.DeltaUTxO.excludingD u
      inputsToExclude
  where
    inputsToExclude :: Set Read.TxIn
    inputsToExclude = Set.fromList (inputs tx)

utxoFromTxOutputs :: Tx -> UTxO
utxoFromTxOutputs tx = Map.fromList $ zip txins txouts
  where
    n :: Int
    n = length (outputs tx)
    txins :: [(Haskell.Data.ByteString.ByteString, Int)]
    txins = map (\ j -> (txid tx, j)) $ [0 .. n - 1]
    txouts :: [Read.TxOut]
    txouts = outputs tx

type IsOurs addr = addr -> Bool

applyTx :: IsOurs Read.Addr -> Tx -> UTxO -> (DeltaUTxO, UTxO)
applyTx isOurs tx u0
  = if
      UTxO.null (UTxO.filterByAddress isOurs (utxoFromTxOutputs tx)) &&
        Cardano.Wallet.Deposit.Pure.DeltaUTxO.null (fst (spendTxD tx u0))
      then (mempty, u0) else
      (fst
         (Cardano.Wallet.Deposit.Pure.DeltaUTxO.receiveD
            (snd (spendTxD tx u0))
            (UTxO.filterByAddress isOurs (utxoFromTxOutputs tx)))
         <> fst (spendTxD tx u0),
       snd
         (Cardano.Wallet.Deposit.Pure.DeltaUTxO.receiveD
            (snd (spendTxD tx u0))
            (UTxO.filterByAddress isOurs (utxoFromTxOutputs tx))))

