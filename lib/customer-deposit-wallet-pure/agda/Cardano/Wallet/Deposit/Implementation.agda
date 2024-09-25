-- | The purpose of this module is for the compiler to check that
-- the specification has been implemented.
--
-- The following pragma indicates that some proofs are still work-in-progress.
-- The specification has been implemented correctly when the following
-- pragma can be successfully removed from this file.
{-# OPTIONS --allow-unsolved-metas #-}

module Cardano.Wallet.Deposit.Implementation where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure using
    ( TxSummary
    ; ValueTransfer
    ; WalletState
    )
open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; Slot
    ; Tx
    ; TxBody
    ; TxId
    ; TxOut
    ; Value
    )
open import Cardano.Wallet.Read.Eras using
    ( Conway
      ; iIsEraConway
    )

import Cardano.Wallet.Deposit.Pure as Wallet
import Cardano.Wallet.Deposit.Read as Read
import Haskell.Data.Map as Map

import Specification

module DepositWallet =
    Specification.DepositWallet
        WalletState
        Address
        (Tx Conway)
        TxBody
        TxId
        Slot
        Value
        ⊤

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}
fromValueTransfer : ValueTransfer → DepositWallet.ValueTransfer
fromValueTransfer x = record
    { spent = spent
    ; received = received
    }
  where
    open ValueTransfer x

fromTxSummary : TxSummary → DepositWallet.TxSummary
fromTxSummary x =
    (Read.slotFromChainPoint txChainPoint , txSummarized , fromValueTransfer txTransfer)
  where
    open TxSummary x

operations : DepositWallet.Operations
operations = record
  { listCustomers = Wallet.listCustomers
  ; createAddress = Wallet.createAddress
  ; availableBalance = Wallet.availableBalance
  ; applyTx = Wallet.applyTx {{iIsEraConway}}
  ; getCustomerHistory = λ customer →
    map fromTxSummary ∘ Wallet.getCustomerHistory customer
  ; createPayment = λ destinations tt s →
    Wallet.createPayment destinations s
  }

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- Helper function
pairFromTxOut : Read.TxOut → (Read.Address × Read.Value)
pairFromTxOut =
    λ txout → (Read.getCompactAddr txout , Read.getValue txout)

@0 properties : DepositWallet.Properties operations
properties = record
    { prop-create-known = Wallet.prop-create-known
    ; deriveAddress = Wallet.deriveCustomerAddress ∘ Wallet.getXPub
    ; prop-create-derive = Wallet.prop-create-derive

    ; summarize = {!  !}
    ; prop-getAddressHistory-summary = {!  !}
    ; prop-tx-known-address = {!   !}

    ; totalValue = Wallet.totalValue
    ; maxFee = Wallet.maxFee
    ; exceeds = λ v1 v2 → Wallet.largerOrEqual v1 v2 ≡ True
    ; _<>_ = _<>_
    ; prop-createPayment-success = {!   !}
    ; outputs = map pairFromTxOut ∘ TxBody.outputs
    ; prop-createPayment-pays = {!   !}
    ; prop-createPayment-not-known =
        λ _ s destinations tx eq1 address eq2 neq3 rel4 →
            Wallet.prop-createPayment-not-known
                s destinations tx eq1 address eq2 neq3
                (subst (Specification._∈_ address) (lem1 (TxBody.outputs tx)) rel4)
    }
  where
    lem1
      : ∀ (xs : List TxOut)
      → map fst (map pairFromTxOut xs)
      ≡ map Read.getCompactAddr xs
    lem1 xs = sym (map-∘ fst pairFromTxOut xs)
