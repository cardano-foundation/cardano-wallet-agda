{-# OPTIONS --erasure #-}
module Cardano.Wallet.Deposit.Read.Temp where

open import Haskell.Prelude

open import Cardano.Wallet.Read public using
    ( CompactAddr
        ; iEqCompactAddr
        ; iOrdCompactAddr
        ; iIsLawfulEqCompactAddr
    ; TxIn
    ; TxOut
    )

{-----------------------------------------------------------------------------
    Address
------------------------------------------------------------------------------}

-- | Default type for addresses on the Cardano ledger.
--
-- Consider using 'CompactAddr' or 'Addr' directly if you want more control
-- over space and time usage.
--
-- NOTE: To be moved into "Cardano.Wallet.Read"
Address = CompactAddr

{-# COMPILE AGDA2HS Address #-}

{-----------------------------------------------------------------------------
    Transactions
------------------------------------------------------------------------------}

-- | Transaction body
--
-- NOTE: To be absorbed by "Cardano.Wallet.Write"
record TxBody : Set where
  constructor TxBodyC
  field
    inputs  : List TxIn
    outputs : List TxOut

open TxBody public

{-# COMPILE AGDA2HS TxBody #-}
