module Cardano.Wallet.Deposit.Pure.DeltaUTxO where

import Cardano.Wallet.Deposit.Pure.UTxO (UTxO)
import qualified Cardano.Wallet.Deposit.Pure.UTxO as UTxO (empty, excluding, excludingS, null, union)
import Cardano.Wallet.Deposit.Read (TxIn)
import Data.Set (Set)
import qualified Haskell.Data.Map as Map (empty, keysSet)
import qualified Haskell.Data.Set as Set (difference, empty, null, union)

data DeltaUTxO = DeltaUTxO{excluded :: Set TxIn, received :: UTxO}

null :: DeltaUTxO -> Bool
null du = Set.null (excluded du) && UTxO.null (received du)

empty :: DeltaUTxO
empty = DeltaUTxO Set.empty Map.empty

apply :: DeltaUTxO -> UTxO -> UTxO
apply du utxo
  = UTxO.union (UTxO.excluding utxo (excluded du)) (received du)

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

appendDeltaUTxO :: DeltaUTxO -> DeltaUTxO -> DeltaUTxO
appendDeltaUTxO da db
  = DeltaUTxO (Set.union (excluded da) excluded'db)
      (UTxO.union received'da (received db))
  where
    received'da :: UTxO
    received'da = UTxO.excluding (received da) (excluded db)
    excluded'db :: Set TxIn
    excluded'db = UTxO.excludingS (excluded db) (received da)

instance Semigroup DeltaUTxO where
    (<>) = appendDeltaUTxO

instance Monoid DeltaUTxO where
    mempty = empty

