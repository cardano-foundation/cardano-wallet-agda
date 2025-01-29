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

open import Specification.Common using (_⇔_; _∈_; isSubsequenceOf)

open import Cardano.Wallet.Address.Encoding using
    ( NetworkTag
    )
open import Cardano.Wallet.Address.BIP32_Ed25519 using
    ( XPub
    )
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
    ( WithOrigin
    ; Slot
    ; Tx
    ; TxId
    ; TxOut
    ; Value
    )
open import Cardano.Wallet.Read using
    ( Conway
      ; iIsEraConway
    )

import Cardano.Wallet.Deposit.Pure.Experimental as Wallet
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Cardano.Wallet.Read as Read
import Data.Map as Map

{-----------------------------------------------------------------------------
    Specification.Cardano
------------------------------------------------------------------------------}

import Specification.Cardano.Chain

SigChain : Specification.Cardano.Chain.Signature
SigChain = record
  { Slot = Read.Slot
  ; iEqSlot = Read.iEqWithOrigin
  ; iOrdSlot = Read.iOrdWithOrigin
  ; iIsLawfulOrdSlot = Read.iIsLawfulOrdWithOrigin
  ; genesis = WithOrigin.Origin
  ; prop-genesis-<= = λ x → {!   !}
  }

import Specification.Cardano.Value

SigValue : Specification.Cardano.Value.Signature
SigValue = record
  { Value = Read.Value
  ; add = Read.add
  ; empty = mempty
  ; iEqValue = Read.iEqValue
  ; largerOrEqual = Read.largerOrEqual
  ; prop-add-x-empty = IsLawfulMonoid.rightIdentity Read.iIsLawfulMonoidValue
  ; prop-add-empty-x = IsLawfulMonoid.leftIdentity Read.iIsLawfulMonoidValue
  ; prop-add-assoc = λ x y z → sym (IsLawfulSemigroup.associativity Read.iIsLawfulSemigroupValue x y z)
  ; prop-add-sym = Read.prop-Value-<>-sym
  ; prop-add-monotone = Read.prop-add-monotone
  }

import Specification.Cardano.Tx

-- Helper function
pairFromTxOut : Read.TxOut → (Read.CompactAddr × Read.Value)
pairFromTxOut =
    λ txout → (Read.getCompactAddr txout , Read.getValue txout)

SigTx : Specification.Cardano.Tx.Signature Read.CompactAddr Read.Value
SigTx = record
  { TxBody = TxBody
  ; Tx = Read.Tx Conway
  ; TxId = Read.TxId
  ; outputs = map pairFromTxOut ∘ TxBody.outputs
  ; getTxId = Read.getTxId
  }

import Specification.Cardano

SigCardano : Specification.Cardano.Signature
SigCardano = record
  { CompactAddr = Address
  ; iEqCompactAddr = Read.iEqCompactAddr
  ; PParams = ⊤
  ; SigChain = SigChain
  ; SigValue = SigValue
  ; SigTx = SigTx
  }

import Specification.Wallet.UTxO

SigWallet : Specification.Wallet.UTxO.Signature SigCardano
SigWallet = record
  { UTxO = UTxO.UTxO
  ; balance = UTxO.balance
  ; applyTxToUTxO = {!   !}
  ; spentTx = {!   !}
  ; receivedTx = {!   !}
  }

{-----------------------------------------------------------------------------
    Module
    DepositWallet
------------------------------------------------------------------------------}

import Specification

module DepositWallet =
    Specification.DepositWallet
        WalletState
        XPub
        SigCardano
        SigWallet

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
  { deriveCustomerAddress = λ xpub addr →
      Wallet.deriveCustomerAddress NetworkTag.MainnetTag xpub addr
  ; fromXPubAndMax = {!   !}
  ; listCustomers = Wallet.listCustomers

  ; getWalletSlot = {!   !}
  ; applyTx = λ slot → Wallet.applyTx {{iIsEraConway}}

  ; totalUTxO = {!   !}
  ; isOurs = {!   !}

  ; getCustomerHistory = λ customer →
    map fromTxSummary ∘ Wallet.getCustomerHistory customer
  ; createPayment = λ destinations tt s →
    Wallet.createPayment destinations s
  }

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}

@0 properties : DepositWallet.Properties operations
properties = record
    { prop-listCustomers-isBijection = {!   !}
    ; prop-listCustomers-fromXPubAndMax-max = {!   !}
    ; prop-listCustomers-fromXPubAndMax-xpub = {!   !}

    ; prop-getWalletSlot-fromXPubAndMax = {!   !}
    ; prop-getWalletSlot-applyTx = {!   !}
    ; prop-getWalletSlot-applyTx-past = {!   !}
    ; prop-listCustomers-applyTx = {!   !}

    ; prop-knownCustomerAddress-isOurs = {!   !}
    ; prop-totalUTxO-applyTx = {!   !}

    ; prop-getCustomerHistory-applyTx = {!   !}
    ; prop-getCustomerHistory-knownCustomer = {!   !}
    ; prop-getCustomerHistory-fromXPubAndMax = {!   !}

    ; prop-createPayment-destinations = {!   !}
    ; prop-createPayment-isOurs = {!   !}
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
