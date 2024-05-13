-- | Definition of 'UTxOHistory'.
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Read using
    ( Slot
    ; SlotNo
    ; TxIn
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Set using
    ( ℙ
    )
open import Haskell.Data.InverseMap using
    ( InverseMap
    )

{-----------------------------------------------------------------------------
    Pruned
------------------------------------------------------------------------------}

-- | The finality of the UTxO history.
data Pruned : Set where
    PrunedUpTo : SlotNo → Pruned
    NotPruned  : Pruned

instance
  iEqPruned : Eq Pruned
  iEqPruned ._==_ NotPruned NotPruned = True
  iEqPruned ._==_ (PrunedUpTo x) (PrunedUpTo y) = x == y
  iEqPruned ._==_ _ _ = False

  iShowPruned : Show Pruned
  iShowPruned = record {Show₂ (record {show = showPruned})}
    where
      showPruned : Pruned → String
      showPruned (PrunedUpTo x) = "PrunedUpTo _"
      showPruned NotPruned = "NotPruned"

{-# COMPILE AGDA2HS Pruned #-}
{-# COMPILE AGDA2HS iEqPruned derive #-}
{-# COMPILE AGDA2HS iShowPruned derive #-}

{-----------------------------------------------------------------------------
    UTxOHistory
------------------------------------------------------------------------------}

-- | UTxO history.
-- Abstract history of the UTxO. We keep track of the creation
-- and spending of slot of each TxIn.
-- This allows us to rollback to a given slot
-- and prune the history to a given slot.
record UTxOHistory : Set where
  field
    history : UTxO
        -- ^ All UTxO , spent and unspent.
    creationSlots : InverseMap TxIn Slot
        -- ^ All TxIn, efficiently indexed by creation slot.
    creationTxIns : Map TxIn Slot
        -- ^ Creation slot of each 'TxIn'.
    spentSlots : InverseMap TxIn SlotNo
        -- ^ All spent 'TxIn', efficiently indexed by spent slot.
    spentTxIns : Map TxIn SlotNo
        -- ^ Spent slot of each spent 'TxIn'.
    tip : Slot
        -- ^ Current tip slot.
    finality : Pruned
        -- ^ Finality slot.
    boot : UTxO
        -- ^ UTxO created at genesis.

open UTxOHistory public

{-# COMPILE AGDA2HS UTxOHistory #-}
