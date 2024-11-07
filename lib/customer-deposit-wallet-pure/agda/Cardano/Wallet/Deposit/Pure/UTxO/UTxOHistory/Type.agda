-- | Definition of 'UTxOHistory'.
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type where

open import Haskell.Prelude

open import Cardano.Wallet.Read using
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
    Types
------------------------------------------------------------------------------}

-- | 'UTxOHistory' represents a history of a UTxO set that can be
-- rolled back (up to the 'finality' point).
--
-- NOTE: This is an abstract data type,
-- its internals are only exported for technical reasons.
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
