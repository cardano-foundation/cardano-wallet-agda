module Cardano.Wallet.Deposit.Pure.UTxO.Tx where

import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    ( DeltaUTxO (excluded, received)
    )
import qualified Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    ( append
    , empty
    , excludingD
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

-- |
-- Remove unspent outputs that are consumed by the given transaction.
-- Also returns a delta.
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

-- |
-- Convert the transaction outputs into a 'UTxO'.
utxoFromTxOutputs :: IsEra era => Tx era -> UTxO
utxoFromTxOutputs = utxoFromEraTx

-- |
-- Tyep for a predicate that tests whether @addr@ belongs to us.
type IsOurs addr = addr -> Bool

-- |
-- Apply a transactions to the 'UTxO'.
--
-- Returns both a delta and the new value.
applyTx
    :: IsEra era
    => IsOurs Read.Addr
    -> Tx era
    -> UTxO
    -> (DeltaUTxO, UTxO)
applyTx isOurs tx u0 =
    if isUnchangedUTxO
        then (Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.empty, u0)
        else (du, u)
  where
    d1 :: (DeltaUTxO, UTxO)
    d1 = spendTxD tx u0
    du10 :: DeltaUTxO
    du10 = fst d1
    u1 :: UTxO
    u1 = snd d1
    receivedUTxO :: UTxO
    receivedUTxO = UTxO.filterByAddress isOurs (utxoFromTxOutputs tx)
    d2 :: (DeltaUTxO, UTxO)
    d2 =
        Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.receiveD
            u1
            receivedUTxO
    du21 :: DeltaUTxO
    du21 = fst d2
    u2 :: UTxO
    u2 = snd d2
    du :: DeltaUTxO
    du = Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.append du21 du10
    u :: UTxO
    u = u2
    isUnchangedUTxO :: Bool
    isUnchangedUTxO =
        UTxO.null receivedUTxO
            && Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO.null du10

-- |
-- A transaction whose inputs have been partially resolved.
data ResolvedTx era = ResolvedTx
    { resolvedTx :: Tx era
    , resolvedInputs :: UTxO
    }

-- |
-- Resolve transaction inputs by consulting a known 'UTxO' set.
resolveInputs :: IsEra era => UTxO -> Tx era -> ResolvedTx era
resolveInputs utxo tx =
    ResolvedTx tx (UTxO.restrictedBy utxo (getInputs tx))

-- |
-- Helper function
--
-- (Internal, exported for technical reasons.)
pairFromTxOut :: TxOut -> (Read.Address, Read.Value)
pairFromTxOut = \txout -> (getCompactAddr txout, getValue txout)

-- |
-- Compute how much 'Value' a 'UTxO' set contains at each address.
groupByAddress :: UTxO -> Map.Map Read.Address Read.Value
groupByAddress =
    Map.fromListWith (<>) . map pairFromTxOut . Map.elems

-- |
-- Compute the 'ValueTransfer' corresponding to 'DeltaUTxO'.
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

-- |
-- Compute the 'ValueTransfer' corresponding to a 'ResolvedTx'.
--
-- Caveat: Spent transaction outputs that have not been resolved
-- will be ignored.
valueTransferFromResolvedTx
    :: IsEra era => ResolvedTx era -> Map.Map Read.Address ValueTransfer
valueTransferFromResolvedTx tx = valueTransferFromDeltaUTxO u0 du
  where
    u0 :: UTxO
    u0 = resolvedInputs tx
    du :: DeltaUTxO
    du = fst (applyTx (\_ -> True) (resolvedTx tx) u0)
