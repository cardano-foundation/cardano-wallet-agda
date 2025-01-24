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
open import Data.Maps.Timeline using
    ( Timeline
    )
open import Data.Map using
    ( Map
    )
open import Data.Set using
    ( ℙ
    )

{-# FOREIGN AGDA2HS
{-# LANGUAGE StrictData #-}
#-}


{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read
    ( Slot
    , SlotNo
    , TxIn
    )
import Data.Map (Map)
import Data.Set (Set)
#-}

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

postulate instance
  iShowUTxOHistory : Show UTxOHistory

{-# COMPILE AGDA2HS UTxOHistory #-}
{-# COMPILE AGDA2HS iShowUTxOHistory derive #-}
