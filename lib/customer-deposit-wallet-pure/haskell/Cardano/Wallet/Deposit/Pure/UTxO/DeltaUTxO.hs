{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO where

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO (UTxO, dom)
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
    ( empty
    , excluding
    , excludingS
    , null
    , union
    )
import Cardano.Wallet.Read.Tx (TxIn)
import Data.Set (Set)
import qualified Haskell.Data.Map as Map (empty)
import qualified Haskell.Data.Set as Set (empty, intersection, null, union)

-- |
-- Representation of a change (delta) to a 'UTxO'.
--
-- The delta records inputs that are excluded, and outputs that are added.
data DeltaUTxO = DeltaUTxO {excluded :: Set TxIn, received :: UTxO}

deriving instance Show DeltaUTxO

-- |
-- Test efficiently whether the change does nothing.
null :: DeltaUTxO -> Bool
null du = Set.null (excluded du) && UTxO.null (received du)

-- |
-- The empty change does nothing.
empty :: DeltaUTxO
empty = DeltaUTxO Set.empty Map.empty

-- |
-- Apply a change to a 'UTxO'.
apply :: DeltaUTxO -> UTxO -> UTxO
apply du utxo =
    UTxO.union (received du) (UTxO.excluding utxo (excluded du))

-- |
-- Variant of 'excluding' that also returns a delta.
excludingD :: UTxO -> Set TxIn -> (DeltaUTxO, UTxO)
excludingD utxo txins = (du, UTxO.excluding utxo txins)
  where
    du :: DeltaUTxO
    du = DeltaUTxO (Set.intersection txins (dom utxo)) UTxO.empty

-- |
-- Variant of 'union' that also returns a delta.
-- The first argument is the 'UTxO' on which the delta acts.
--
-- > receiveD old new
receiveD :: UTxO -> UTxO -> (DeltaUTxO, UTxO)
receiveD old new = (du, UTxO.union new old)
  where
    du :: DeltaUTxO
    du = DeltaUTxO Set.empty new

-- |
-- Combine two deltas: Apply @x@ /after/ applying @y@.
-- Drops inputs that were created by @y@, but removed again by @x@
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

-- |
-- Combine a sequence of 'DeltaUTxO' using `append`
concat :: [DeltaUTxO] -> DeltaUTxO
concat = foldr append empty
