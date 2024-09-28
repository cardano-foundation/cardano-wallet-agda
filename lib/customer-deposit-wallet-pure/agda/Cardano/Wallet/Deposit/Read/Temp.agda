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

Addr = CompactAddr
Address = Addr

{-# COMPILE AGDA2HS Addr #-}
{-# COMPILE AGDA2HS Address #-}

{-----------------------------------------------------------------------------
    Transactions
------------------------------------------------------------------------------}

record TxBody : Set where
  constructor TxBodyC
  field
    inputs  : List TxIn
    outputs : List TxOut

open TxBody public

{-# COMPILE AGDA2HS TxBody #-}
