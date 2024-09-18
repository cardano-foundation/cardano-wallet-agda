module Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO where

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
    ( empty
    , excluding
    , excludingS
    , null
    , union
    )
import Cardano.Wallet.Read.Tx (TxIn)
import Data.Set (Set)
import qualified Haskell.Data.Map as Map (empty, keysSet)
import qualified Haskell.Data.Set as Set (difference, empty, null, union)

data DeltaUTxO = DeltaUTxO {excluded :: Set TxIn, received :: UTxO}

null :: DeltaUTxO -> Bool
null du = Set.null (excluded du) && UTxO.null (received du)

empty :: DeltaUTxO
empty = DeltaUTxO Set.empty Map.empty

apply :: DeltaUTxO -> UTxO -> UTxO
apply du utxo =
    UTxO.union (UTxO.excluding utxo (excluded du)) (received du)

excludingD :: UTxO -> Set TxIn -> (DeltaUTxO, UTxO)
excludingD utxo txins = (du, UTxO.excluding utxo txins)
  where
    du :: DeltaUTxO
    du = DeltaUTxO (Set.difference (Map.keysSet utxo) txins) UTxO.empty

receiveD :: UTxO -> UTxO -> (DeltaUTxO, UTxO)
receiveD old new = (du, UTxO.union old new)
  where
    du :: DeltaUTxO
    du = DeltaUTxO Set.empty new

append :: DeltaUTxO -> DeltaUTxO -> DeltaUTxO
append x y =
    DeltaUTxO
        (Set.union excluded'x (excluded y))
        (UTxO.union (received x) received'y)
  where
    excluded'x :: Set TxIn
    excluded'x = UTxO.excludingS (excluded x) (received y)
    received'y :: UTxO
    received'y = UTxO.excluding (received y) (excluded x)
