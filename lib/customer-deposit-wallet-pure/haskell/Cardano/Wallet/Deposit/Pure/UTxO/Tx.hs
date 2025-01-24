{-# LANGUAGE StrictData #-}

module Cardano.Wallet.Deposit.Pure.UTxO.Tx
    ( -- * Applying Transactions to UTxO
      IsOurs
    , applyTx

      -- * Resolved Transactions
    , ResolvedTx (..)
    , resolveInputs

      -- * Value transfer from transactions
    , valueTransferFromDeltaUTxO
    , valueTransferFromResolvedTx
    )
where

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
import Cardano.Wallet.Read.Address ()
import qualified Cardano.Wallet.Read.Address as Read (CompactAddr)
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx (IsValid (IsValidC), Tx, TxIn, TxOut)
import qualified Cardano.Wallet.Read.Tx as Read
    ( getCollateralInputs
    , getCompactAddr
    , getInputs
    , getScriptValidity
    , getValue
    , utxoFromEraTx
    )
import Cardano.Wallet.Read.Value ()
import qualified Cardano.Wallet.Read.Value as Read (Value)
import qualified Data.Map as Map (Map, elems, fromListWith, map, unionWith)
import Data.Set (Set)
import Prelude hiding (null, subtract)

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
        case Read.getScriptValidity tx of
            IsValidC True -> Read.getInputs tx
            IsValidC False -> Read.getCollateralInputs tx

-- |
-- Convert the transaction outputs into a 'UTxO'.
utxoFromTxOutputs :: IsEra era => Tx era -> UTxO
utxoFromTxOutputs = Read.utxoFromEraTx

-- |
-- Type for a predicate that tests whether @addr@ belongs to us.
type IsOurs addr = addr -> Bool

-- |
-- Apply a transactions to the 'UTxO'.
--
-- Returns both a delta and the new value.
applyTx
    :: IsEra era
    => IsOurs Read.CompactAddr
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
    ResolvedTx tx (UTxO.restrictedBy utxo (Read.getInputs tx))

-- |
-- Helper function
--
-- (Internal, exported for technical reasons.)
pairFromTxOut :: TxOut -> (Read.CompactAddr, Read.Value)
pairFromTxOut =
    \txout -> (Read.getCompactAddr txout, Read.getValue txout)

-- |
-- Compute how much 'Value' a 'UTxO' set contains at each address.
groupByAddress :: UTxO -> Map.Map Read.CompactAddr Read.Value
groupByAddress =
    Map.fromListWith (<>) . map pairFromTxOut . Map.elems

-- |
-- Compute the 'ValueTransfer' corresponding to 'DeltaUTxO'.
valueTransferFromDeltaUTxO
    :: UTxO -> DeltaUTxO -> Map.Map Read.CompactAddr ValueTransfer
valueTransferFromDeltaUTxO u0 du = Map.unionWith (<>) ins outs
  where
    u1 :: UTxO
    u1 = UTxO.restrictedBy u0 (excluded du)
    ins :: Map.Map Read.CompactAddr ValueTransfer
    ins = Map.map fromSpent (groupByAddress u1)
    outs :: Map.Map Read.CompactAddr ValueTransfer
    outs = Map.map fromReceived (groupByAddress (received du))

-- |
-- Compute the 'ValueTransfer' corresponding to a 'ResolvedTx'.
--
-- Caveat: Spent transaction outputs that have not been resolved
-- will be ignored.
valueTransferFromResolvedTx
    :: IsEra era
    => ResolvedTx era
    -> Map.Map Read.CompactAddr ValueTransfer
valueTransferFromResolvedTx tx = valueTransferFromDeltaUTxO u0 du
  where
    u0 :: UTxO
    u0 = resolvedInputs tx
    du :: DeltaUTxO
    du = fst (applyTx (\_ -> True) (resolvedTx tx) u0)
