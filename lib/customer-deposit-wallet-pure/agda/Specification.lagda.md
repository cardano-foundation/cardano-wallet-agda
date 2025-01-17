# Specification: Customer Deposit Wallet

## Synopsis

🚧 DRAFT 2025-01-17

This document specifies the core functionality of a **customer deposit wallet**,
or **deposit wallet** for short.

A deposit wallet allows you to track the **origin of incoming funds**:
Each customer is assigned a unique address belonging to the wallet;
a deposit made at this address is treated as originating from the customer.

However, outgoing funds are not distinguished by customer
— once funds have gone into the wallet,
they are all part of a **single wallet balance**.

A deposit wallet is useful for businesses such
as centralized exchanges (CEX) or e-shops on Cardano.

Technically, each customer is represented by a numerical index (natural number).
The deposit wallet manages a mapping between indices and addresses,
and tracks incoming funds for each known address.

# Setup

This document is a [literate Agda][lagda] file: It contains prose that
describes and explains the specification, but it also contains definitions
and logical properties that can be checked by the proof assistant [Agda][].

When implementing this specification,
we intend to create a **machine-checked proof**
that our implementation matches this specification.
However, this specification only covers the **core functionality** of
the software application to be implemented, not the full software.
We proceed as follows:

* The full software application will be implemented in [Haskell][].
  Sizeable parts of the functionality will be tested, not proven.

* However, the core functionality that is covered by this specification
  will be implemented using [Agda][] and exported to Haskell
  via the [agda2hs][] transpiler.
  This core functionality will be proven, not tested.

* In turn, proofs about the core functionality will depend on the
  assumption that more basic data types provided by Haskell libraries,
  such as the [Data.Set][containers] type,
  have implementations that match a specification.
  For the time being, we accept that this is an assumption
  and that the library implementations have only been tested.
  We `postulate` specifications in Agda as far as needed.

  [agda]: https://github.com/agda/agda
  [lagda]: https://agda.readthedocs.io/en/v2.6.4/tools/literate-programming.html
  [agda2hs]: https://github.com/agda/agda2hs
  [haskell]: https://www.haskell.org
  [containers]: https://hackage.haskell.org/package/containers-0.7/docs/Data-Set.html

```agda
module Specification where
```

## Imports

In order to formulate the specification, we need to import standard Haskell vocabulary:

```agda
open import Haskell.Prelude
open import Haskell.Reasoning
```

and also

* [Specification.Common](Specification/Common.lagda.md)
  — Minor additional Haskell concepts.

In addition, we need to import concepts that are specific to Cardano:

* [Specification.Value](Specification/Value.lagda.md)
  — Monetary `Value`.

<!--
```agda
open import Haskell.Data.Word.Odd using (Word31)

open import Specification.Common using (_⇔_; _∈_; isSubsetOf)

import Specification.Value
```
-->

# Specification

## Overview

This specification of a **customer deposit wallet**
amounts to the specification of an abstract data type `WalletState`,
which represents the entire state of such a wallet.

The goal of this document is to specify the operations
on this abstract data type and the logical properties that relate them.

We define a `module` `DepositWallet` which is parametrized by
several definitions from the Cardano ledger,
but also by the abstract data type `WalletState` that we wish to specify.

```agda
module
  DepositWallet
    (WalletState : Set)
    (Address : Set)
    {{_ : Eq Address}}
    (Tx : Set)
    (TxBody : Set)
    (TxId : Set)
    (Slot : Set)
    (ValueSig : Specification.Value.Signature)
    (PParams : Set)
  where

  open Specification.Value.Signature ValueSig
```

## Operations

We now list all auxiliary data types and all
operations supported by the abstract data type `WalletState`.
This list is meant for reference
— we will explain each of them in detail in the subsequent sections.

Auxiliary data types:

```agda
  Customer = Word31

  record ValueTransfer : Set where
    field
      spent    : Value
      received : Value

  open ValueTransfer

  TxSummary : Set
  TxSummary = Slot × TxId × ValueTransfer
```

Operations:

```agda
  record Operations : Set where
    field

      listCustomers : WalletState → List (Customer × Address)
      createAddress : Customer → WalletState → (Address × WalletState)

      availableBalance : WalletState → Value
      applyTx : Tx → WalletState → WalletState

      getCustomerHistory : WalletState → Customer → List TxSummary

      createPayment
        : List (Address × Value)
        → PParams → WalletState → Maybe TxBody
```

## Properties

In subsequent sections, we will specify the properties that
the operations should satisfy.

The following record collects the properties:

```agda
  record Properties
      (O : Operations)
      : Set₁
    where
    open Operations O
```

(For some reason, it needs to be in `Set₁`.)

### Mapping between Customers and Address

The type `Customer` denotes a unique identier for a customer.
For reasons explained later, we choose to represent this type
as numerical indices, i.e. natural numbers:

    Customer = Nat

The mapping between customers and addresses will be queried and established with
the following operations:

    listCustomers : WalletState → List (Customer × Address)
    createAddress : Customer → WalletState → (Address × WalletState)

Here, `listCustomers` lists all customer/address pairs that have been mapped to each other so far.
In turn, `createAddress` adds a new customer/address to the mapping.

In order to express how these functions are related, we define

```agda
    knownCustomer : Customer → WalletState → Bool
    knownCustomer c = elem c ∘ map fst ∘ listCustomers

    knownCustomerAddress : Address → WalletState → Bool
    knownCustomerAddress address = elem address ∘ map snd ∘ listCustomers
```

Here, a `knownCustomer` is a `Customer` that appears in the result of `listCustomers`,
while `knownCustomerAddress` is an `Address` that appears in the result.
Note that a deposit wallet may own additional `Addresses` not included here,
such as change addresses — but these addresses are not customer addresses.

The two operations are related by the property

```agda
    field

      prop-create-known
        : ∀(c : Customer) (s0 : WalletState)
        → let (address , s1) = createAddress c s0
          in  knownCustomerAddress address s1 ≡ True
```

### Address derivation

For compatibility with hardware wallets and the [BIP-32][] standard,
we derive the `Address` of each customer from the root private key
of the wallet in a deterministic fashion:

```agda
      deriveAddress : WalletState → (Customer → Address)

      prop-create-derive
        : ∀(c : Customer) (s0 : WalletState)
        → let (address , _) = createAddress c s0
          in  deriveAddress s0 c ≡ address
```

Specifically, in the notation of [BIP-32][], we use

  	deriveAddress : WalletState → Nat → Address
	  deriveAddress s ix = rootXPrv s / 1857' / 1815' / 0' / 0 / ix

Here, `1857` is a new “purpose” identifier; we cannot reuse the [CIP-1852][] standard, because it behaves differently when discovering funds in blocks.

  [bip-32]: https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki
  [cip-1852]: https://cips.cardano.org/cips/cip1852/

This method of deriving addresses is also the reason why we choose
a concrete representation of `Customer` as a natural number.

### Applying transactions

TODO: Specification of total wallet funds.
Amounts to rewrite of the original wallet specification
by Edsko and Duncan in Agda. To be specified in a separate document.

    availableBalance : WalletState → Value
    applyTx : Tx → WalletState → WalletState

### Tracking incoming funds

Beyond assigning an address to a customer,
the new wallet state returned by `createAddress`
also tracks this address whenever new blocks are incorporated into the wallet state.
For this purpose of tracking, we introduce an operation

    getCustomerHistory : WalletState → Customer → List TxSummary

which returns a list of transaction summaries. For a given transaction, such a summary reports the total `Value` spend or received at a specific address.

    record ValueTransfer : Set where
      field
        spent    : Value
        received : Value

    open ValueTransfer

    TxSummary : Set
    TxSummary = Slot × TxId × ValueTransfer

Note that `Value` includes both native coins (ADA) and
user-defined assets, such as stablecoins NFTs.
Also note that the customer deposit wallet does not support
delegation and reward accounts, and the `spent` value
can only be spent from transaction outputs.

The function `getCustomerHistory` allows users to detect incoming
transfers by observing the `received` value.

The behavior of this function is best specified in terms of a function

```agda
      summarize : WalletState → Tx → List (Address × TxSummary)

    getAddressSummary
      : Address → List (Address × TxSummary) → List TxSummary
    getAddressSummary address =
      map snd ∘ filter (λ x → fst x == address)
```

which summarizes a single transaction. Specifically, the result of `getCustomerHistory` an aggregate of all previous transaction summaries.

```agda
    field
      prop-getAddressHistory-summary
        : ∀ (s : WalletState)
            (c : Customer)
            (address : Address)
            (tx : Tx)
        → (c , address) ∈ listCustomers s
        → getCustomerHistory (applyTx tx s) c
          ≡ (getAddressSummary address (summarize s tx))
              ++ getCustomerHistory s c
```

Importantly, we only track an address if and only if it is a `knownCustomerAddress`.

```agda
      prop-tx-known-address
        : ∀ (address : Address)
            (s : WalletState)
            (tx : Tx)
        → (knownCustomerAddress address s ≡ True)
        ⇔ (address ∈ map fst (summarize s tx))
```

### Creating transactions

Finally, we expose an operation

    createPayment
      : List (Address × Value)
      → PParams → WalletState → Maybe Tx

which constructs a transaction that sends given values to given addresses.
Here, `PParams` are protocol parameters needed for computation the fee to
include in the `Tx`.

First, as the main purpose of a wallet is to be able to send funds,
it would be most desirable to require that this function always **succeeds**
in creating a transaction provided that the wallet has **sufficient funds**.
Unfortunately, however, we do not yet have an implementation
where we can prove this property. This topic is discussed in

* [Specification.Wallet.Payment](Specification/Wallet/Payment.lagda.md)

Second, the transaction sends funds as indicated

```agda
    field
      outputs : TxBody → List (Address × Value)

    field
      prop-createPayment-pays
        : ∀ (s : WalletState)
            (pp : PParams)
            (destinations : List (Address × Value))
            (tx : TxBody)
          → createPayment destinations pp s ≡ Just tx
          → isSubsetOf (outputs tx) destinations ≡ True
```

Third, and most importantly, the operation `createPayment` never creates a transaction
whose `received` summary for any tracked index/address pair is non-zero.
In other words, `createPayment` uses change addresses that are distinct
from any address obtained via `createAddress`.

That said, `createPayment` is free to contribute to the `spent` summary of any address
— the deposit wallet spends funds from any address as it sees fit.

In other words, we have

```agda
    getAddress : (Address × Value) → Address
    getAddress = fst

    field
      prop-createPayment-not-known
        : ∀ (pp : PParams)
            (s  : WalletState)
            (destinations : List (Address × Value))
            (tx : TxBody)
        → createPayment destinations pp s ≡ Just tx
        → ∀ (address : Address)
          → knownCustomerAddress address s ≡ True
          → ¬ (address ∈ map fst destinations)
          → ¬ (address ∈ map getAddress (outputs tx))
```

## Derived Properties

TODO
From the properties above, one can prove various other properties.
However, this requires and induction principle on `WalletState`,
where we can be certain that other operations do not interfere
with the given ones.

```agda
{-
prop-getAddressHistory-unknown : Set
prop-getAddressHistory-unknown
  = ∀ (s : WalletState)
      (addr : Address)
  → knownAddress addr s ≡ False
  → getAddressHistory addr s ≡ []
-}
```

