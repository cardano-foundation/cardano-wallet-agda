-- | Definition of 'UTxOHistory'.
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Read using
    ( Slot
    ; SlotNo
    ; TxIn
    )
open import Cardano.Wallet.Deposit.Pure.RollbackWindow using
    ( RollbackWindow
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Maps.Timeline using
    ( Timeline
    )
open import Haskell.Data.Set using
    ( ℙ
    )

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
    created : Timeline Slot TxIn
        -- ^ Creation slots of the TxIn, spent and unspent.
    spent : Timeline SlotNo TxIn
        -- ^ Spending slot number of the TxIn, spent.
    window : RollbackWindow Slot
        -- ^ Current rollback window.
    boot : UTxO
        -- ^ UTxO created at genesis.

open UTxOHistory public

{-# COMPILE AGDA2HS UTxOHistory #-}
