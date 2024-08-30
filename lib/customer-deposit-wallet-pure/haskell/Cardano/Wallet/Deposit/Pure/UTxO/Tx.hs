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
import qualified Cardano.Wallet.Deposit.Read as Read (Addr, Address)
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx
    ( IsValid (IsValidC)
    , Tx
    , TxIn
    , TxOut
    , getCollateralInputs
    , getCompactAddr
    , getInputs
    , getScriptValidity
    , getValue
    , utxoFromEraTx
    )
import qualified Cardano.Wallet.Read.Value as Read (Value)
import Data.Set (Set)
import qualified Haskell.Data.Map as Map
    ( Map
    , elems
    , fromListWith
    , map
    , unionWith
    )

spendTxD :: IsEra era => Tx era -> UTxO -> (DeltaUTxO, UTxO)
spendTxD tx u =
    Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.excludingD
        u
        inputsToExclude
  where
    inputsToExclude :: Set TxIn
    inputsToExclude =
        case getScriptValidity tx of
            IsValidC True -> getInputs tx
            IsValidC False -> getCollateralInputs tx

utxoFromTxOutputs :: IsEra era => Tx era -> UTxO
utxoFromTxOutputs = utxoFromEraTx

type IsOurs addr = addr -> Bool

applyTx
    :: IsEra era
    => IsOurs Read.Addr
    -> Tx era
    -> UTxO
    -> (DeltaUTxO, UTxO)
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

data ResolvedTx era = ResolvedTx
    { resolvedTx :: Tx era
    , resolvedInputs :: UTxO
    }

resolveInputs :: IsEra era => UTxO -> Tx era -> ResolvedTx era
resolveInputs utxo tx =
    ResolvedTx tx (UTxO.restrictedBy utxo (getInputs tx))

pairFromTxOut :: TxOut -> (Read.Address, Read.Value)
pairFromTxOut = \txout -> (getCompactAddr txout, getValue txout)

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
    :: IsEra era => ResolvedTx era -> Map.Map Read.Address ValueTransfer
valueTransferFromResolvedTx tx = valueTransferFromDeltaUTxO u0 du
  where
    u0 :: UTxO
    u0 = resolvedInputs tx
    du :: DeltaUTxO
    du = fst (applyTx (\_ -> True) (resolvedTx tx) u0)
