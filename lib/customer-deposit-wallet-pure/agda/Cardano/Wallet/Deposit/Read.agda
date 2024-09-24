{-# OPTIONS --erasure #-}
module Cardano.Wallet.Deposit.Read where

open import Haskell.Prelude

open import Cardano.Wallet.Read.Address public
open import Cardano.Wallet.Read.Eras public
open import Cardano.Wallet.Read.Block public
open import Cardano.Wallet.Read.Chain public
open import Cardano.Wallet.Read.Tx public
open import Cardano.Wallet.Read.Value public

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read.Value 
    ( Value
    )
#-}

import Haskell.Data.Map as Map

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

{-----------------------------------------------------------------------------
    Block
------------------------------------------------------------------------------}
getEraTransactions : {{IsEra era}} → Block era → List (Tx era)
getEraTransactions block = []

{-# COMPILE AGDA2HS getEraTransactions #-}
