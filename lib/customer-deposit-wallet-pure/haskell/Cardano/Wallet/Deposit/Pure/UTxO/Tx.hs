module Cardano.Wallet.Deposit.Pure.UTxO.Tx where

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    ( DeltaUTxO (excluded, received)
    )
import qualified Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    ( excludingD
    , null
    , receiveD
    )
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
    ( filterByAddress
    , null
    , restrictedBy
    )
import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer
    ( ValueTransfer
    , fromReceived
    , fromSpent
    )
import Cardano.Wallet.Deposit.Read (Tx (txbody, txid), TxBody (inputs, outputs))
import qualified Cardano.Wallet.Deposit.Read as Read
    ( Addr
    , Address
    , TxIn
    , TxOut (address, value)
    )
import qualified Cardano.Wallet.Deposit.Read.Value as Read (Value)
import Data.Set (Set)
import qualified Haskell.Data.ByteString (ByteString)
import qualified Haskell.Data.Map as Map
    ( Map
    , elems
    , fromList
    , fromListWith
    , map
    , unionWith
    )
import qualified Haskell.Data.Set as Set (fromList)

spendTxD :: Tx -> UTxO -> (DeltaUTxO, UTxO)
spendTxD tx u =
    Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.excludingD
        u
        inputsToExclude
  where
    inputsToExclude :: Set Read.TxIn
    inputsToExclude = Set.fromList (inputs (txbody tx))

utxoFromTxOutputs :: Tx -> UTxO
utxoFromTxOutputs tx = Map.fromList $ zip txins txouts
  where
    n :: Int
    n = length (outputs (txbody tx))
    txins :: [(Haskell.Data.ByteString.ByteString, Int)]
    txins = map (\j -> (txid tx, j)) $ [0 .. n - 1]
    txouts :: [Read.TxOut]
    txouts = outputs (txbody tx)

type IsOurs addr = addr -> Bool

applyTx :: IsOurs Read.Addr -> Tx -> UTxO -> (DeltaUTxO, UTxO)
applyTx isOurs tx u0 =
    if UTxO.null (UTxO.filterByAddress isOurs (utxoFromTxOutputs tx))
        && Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.null
            (fst (spendTxD tx u0))
        then (mempty, u0)
        else
            ( fst
                ( Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.receiveD
                    (snd (spendTxD tx u0))
                    (UTxO.filterByAddress isOurs (utxoFromTxOutputs tx))
                )
                <> fst (spendTxD tx u0)
            , snd
                ( Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.receiveD
                    (snd (spendTxD tx u0))
                    (UTxO.filterByAddress isOurs (utxoFromTxOutputs tx))
                )
            )

data ResolvedTx = ResolvedTx
    { resolvedTx :: Tx
    , resolvedInputs :: UTxO
    }

resolveInputs :: UTxO -> Tx -> ResolvedTx
resolveInputs utxo tx =
    ResolvedTx
        tx
        (UTxO.restrictedBy utxo (Set.fromList (inputs (txbody tx))))

pairFromTxOut :: Read.TxOut -> (Read.Address, Read.Value)
pairFromTxOut = \txout -> (Read.address txout, Read.value txout)

groupByAddress :: UTxO -> Map.Map Read.Address Read.Value
groupByAddress =
    Map.fromListWith (<>) . map pairFromTxOut . Map.elems

valueTransferFromDeltaUTxO
    :: UTxO -> DeltaUTxO -> Map.Map Read.Address ValueTransfer
valueTransferFromDeltaUTxO u0 du = Map.unionWith (<>) ins outs
  where
    u1 :: UTxO
    u1 = UTxO.restrictedBy u0 (excluded du)
    ins :: Map.Map Read.Address ValueTransfer
    ins = Map.map fromSpent (groupByAddress u1)
    outs :: Map.Map Read.Address ValueTransfer
    outs = Map.map fromReceived (groupByAddress (received du))

valueTransferFromResolvedTx
    :: ResolvedTx -> Map.Map Read.Address ValueTransfer
valueTransferFromResolvedTx tx = valueTransferFromDeltaUTxO u0 du
  where
    u0 :: UTxO
    u0 = resolvedInputs tx
    du :: DeltaUTxO
    du = fst (applyTx (\_ -> True) (resolvedTx tx) u0)
