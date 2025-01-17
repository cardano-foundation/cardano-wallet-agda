-- | The purpose of this module is for the compiler to check that
-- the specification has been implemented.
--
-- The following pragma indicates that some proofs are still work-in-progress.
-- The specification has been implemented correctly when the following
-- pragma can be successfully removed from this file.
{-# OPTIONS --allow-unsolved-metas #-}

module Implementation where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Specification.Common using (_⇔_; _∈_; isSubsetOf)

open import Cardano.Wallet.Deposit.Pure.Experimental using
    ( TxSummary
    ; ValueTransfer
    ; WalletState
    )
open import Cardano.Wallet.Deposit.Read.Temp using
    ( Address
    ; TxBody
    )
open import Cardano.Wallet.Read using
    ( Slot
    ; Tx
    ; TxId
    ; TxOut
    ; Value
    )
open import Cardano.Wallet.Read.Eras using
    ( Conway
      ; iIsEraConway
    )

import Cardano.Wallet.Deposit.Pure.Experimental as Wallet
import Cardano.Wallet.Read as Read
import Haskell.Data.Map as Map

{-----------------------------------------------------------------------------
    Signature
    Value
------------------------------------------------------------------------------}

import Specification.Value

ValueSig : Specification.Value.Signature
ValueSig = record
  { Value = Read.Value
  ; add = Read.add
  ; iEqValue = Read.iEqValue
  ; largerOrEqual = Read.largerOrEqual
  ; prop-add-assoc = λ x y z → sym (IsLawfulSemigroup.associativity Read.iIsLawfulSemigroupValue x y z)
  ; prop-add-sym = Read.prop-Value-<>-sym
  ; prop-add-monotone = Read.prop-add-monotone
  }

{-----------------------------------------------------------------------------
    Module
    DepositWallet
------------------------------------------------------------------------------}

import Specification

module DepositWallet =
    Specification.DepositWallet
        WalletState
        Address
        (Tx Conway)
        TxBody
        TxId
        Slot
        ValueSig
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
pairFromTxOut : Read.TxOut → (Read.CompactAddr × Read.Value)
pairFromTxOut =
    λ txout → (Read.getCompactAddr txout , Read.getValue txout)

@0 properties : DepositWallet.Properties operations
properties = record
    { prop-create-known = Wallet.prop-create-known
    ; deriveAddress = λ s →
        Wallet.deriveCustomerAddress (Wallet.getNetworkTag s) (Wallet.getXPub s)
    ; prop-create-derive = Wallet.prop-create-derive

    ; summarize = {!  !}
    ; prop-getAddressHistory-summary = {!  !}
    ; prop-tx-known-address = {!   !}

    ; outputs = map pairFromTxOut ∘ TxBody.outputs
    ; prop-createPayment-pays = {!   !}
    ; prop-createPayment-not-known =
        λ _ s destinations tx eq1 address eq2 neq3 rel4 →
            Wallet.prop-createPayment-not-known
                s destinations tx eq1 address eq2 neq3
                (subst (_∈_ address) (lem1 (TxBody.outputs tx)) rel4)
    }
  where
    lem1
      : ∀ (xs : List TxOut)
      → map fst (map pairFromTxOut xs)
      ≡ map Read.getCompactAddr xs
    lem1 xs = sym (map-∘ fst pairFromTxOut xs)
