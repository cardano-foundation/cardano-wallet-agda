# Specification: Customer Deposit Wallet

## Synopsis

🚧 DRAFT 2025-01-20

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

Technically, each customer is represented by a numerical index starting at `0`.
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

In order to formulate the specification, we need to import standard Haskell vocabulary

```agda
open import Haskell.Prelude
open import Haskell.Reasoning
```

and also

* [Specification.Common](Specification/Common.lagda.md)
  — Minor additional Haskell concepts.

In addition, we also need to import concepts that are specific to Cardano:

* [Specification.Cardano](Specification/Cardano.lagda.md)
  * [Specification.Cardano.Tx](Specification/Cardano/Value.lagda.md)
  — Transaction type `Tx`.
  * [Specification.Cardano.Value](Specification/Cardano/Value.lagda.md)
  — Monetary `Value`. Includes both native coins (ADA) and
user-defined assets, such as stablecoins or NFTs.

<!--
```agda
open import Haskell.Data.Word.Odd using (Word31)

open import Specification.Common using
  (_⇔_; _∈_; isSubsetOf; isJust; nub)

import Specification.Cardano
import Specification.Wallet.UTxO
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

* the abstract data type `WalletState` that we wish to specify,
* an implementation `SigCardano` of concepts that are related to Cardano,
and which we need to express the specification.
* a specification `SigWallet` of wallet-related concepts that are
  not the focus of this document, and

```agda
module
  DepositWallet
    (WalletState : Set)
    (XPub : Set)
    (SigCardano : Specification.Cardano.Signature)
    (SigWallet  : Specification.Wallet.UTxO.Signature SigCardano)
  where

  open Specification.Cardano.Signature SigCardano
  open Specification.Wallet.UTxO.Signature SigWallet
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

      deriveCustomerAddress : XPub → Customer → Address
      fromXPubAndMax        : XPub → Word31 → WalletState
      listCustomers         : WalletState → List (Customer × Address)

      totalUTxO : WalletState → UTxO
      applyTx   : Tx → WalletState → WalletState
      isOurs    : WalletState → Address → Bool

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
  record Properties (O : Operations) : Set₁ where
    open Operations O
```

### Mapping between Customers and Address

The type `Customer` denotes a unique identifier for a customer.
For reasons explained later, we choose to represent this type
as numerical indices:

    Customer = Word31

The mapping between customers and addresses is maintained by
the following operations:

    deriveCustomerAddress : XPub → Customer → Address

    fromXPubAndMax        : XPub → Word31 → WalletState
    listCustomers         : WalletState → List (Customer × Address)

Here

* `deriveCustomerAddress` deterministically creates an address
  for a given customer index.

* `fromXPubAndMax xpub cmax` creates an empty `WalletState`
  at genesis which keeps track of customers indices `0` to `cmax`.
  Their addresses are derived deterministically from the public key `xpub`.

* `listCustomers` returns the mapping between customers and addresses
  currently maintained by the `WalletState`.

In order to make the specification clear and simple,
we do not allow the mapping between customers and addresses
to change after creation
— the idea is that `listCustomers` will always return the same result,
no matter how the `WalletState` is changed subsequently.

The result of the function `listCustomers` contains
the entire mapping between customers and addresses.
The following definitions make this mapping easier to discuss:

```agda
    customerAddress : Customer → WalletState → Maybe Address
    customerAddress c = lookup c ∘ listCustomers

    knownCustomer : Customer → WalletState → Bool
    knownCustomer c = isJust ∘ customerAddress c

    knownCustomerAddress : Address → WalletState → Bool
    knownCustomerAddress a = elem a ∘ map snd ∘ listCustomers
```

We require that the mapping is a bijection

```agda
    unique : {{Eq a}} → List a → Bool
    unique xs = nub xs == xs

    isBijection : ∀ {{_ : Eq a}} {{_ : Eq b}} → List (a × b) → Bool
    isBijection xys = unique (map fst xys) && unique (map snd xys)

    field
      prop-listCustomers-isBijection
        : ∀ (s : WalletState)
        → isBijection (listCustomers s) ≡ True
```

The relation between `listCustomers` and `fromXPubAndMax`
is specified as follows:

First, the mapping precisely contains customers indices `0` to `count - 1`:

```agda
      prop-listCustomers-fromXPubAndMax-max
        : ∀ (c : Customer) (xpub : XPub) (cmax : Word31)
        → knownCustomer c (fromXPubAndMax xpub cmax)
          ≡ (0 <= c && c <= cmax)
```

Second, the addresses are derived deterministically from
the public key and the customer index.

```agda
      prop-listCustomers-fromXPubAndMax-xpub
        : ∀ (c : Customer) (xpub : XPub) (cmax : Word31) (addr : Address)
        → customerAddress c (fromXPubAndMax xpub cmax)
          ≡ Just addr
        → deriveCustomerAddress xpub c
          ≡ addr
```

The idea is that these properties hold not only for the initial state
at `fromXPubAndMax`, but also for any state obtained through
other operations such as `applyTx`.

For compatibility with hardware wallets and the [BIP-32][] standard,
we derive the `Address` of each customer from the root private key
of the wallet in a deterministic fashion.
Specifically, using the notation of [BIP-32][] in pseudo-code,
we require that

  	deriveCustomerAddress : WalletState → Word31 → Address
	  deriveCustomerAddress s ix = rootXPrv s / 1857' / 1815' / 0' / 0 / ix

Here, `1857` is a new “purpose” identifier; we cannot reuse the [CIP-1852][] standard, because it behaves differently when discovering funds in blocks.

  [bip-32]: https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki
  [cip-1852]: https://cips.cardano.org/cips/cip1852/

This method of deriving addresses is also the reason why we choose
a concrete representation of `Customer` as `Word31`.

### Wallet balance and transactions

The primary purpose of a wallet is to keep track of funds
that are available for spending.

On the Cardano blockchain,
this means keeping track of unspent transaction outputs (UTxO).
This topic is discussed in more detail in

* [Specification.Wallet.UTxO](Specification/Wallet/UTxO.lagda.md)

Here, we only introduce basic concepts of UTxO management,
as we want to focus on the relation between customer addresses
and funds in the wallet.

The basics of `UTxO` managed are as follows:
The total UTxO of the wallet that can be spent is provided by the function

    totalUTxO : WalletState → UTxO

A transaction of type `Tx` may spend some outputs
and create new ones.
The function

    applyTxToUTxO : (Address → Bool) → Tx → UTxO → UTxO

applies the transaction to the `UTxO`.
Here, the first argument is a predicate that specifies which output
addresses of a transactions belong to the wallet.
For the Deposit Wallet, we derive this from the wallet state as

    isOurs : WalletState → Address → Bool


Now, we discuss the entire `WalletState`.
First, we consider the predicate `isOurs`.
We require that all known customer addresses belong to the wallet

```agda
      prop-knownCustomerAddress-isOurs
        : ∀ (addr : Address) (s : WalletState)
        → knownCustomerAddress addr s ≡ True
        → isOurs s addr ≡ True
```

However, there may be additional addresses belonging to the wallet,
in particular change addresses.

In order to apply a `Tx` to the entire `WalletState`,
we use the function

    applyTx : WalletState → Tx → UTxO → UTxO

We require that this function
is equivalent to `applyTxToUTxO` on the `totalUTxO`:

```agda
      prop-totalUTxO-applyTx
        : ∀ (s : WalletState) (tx : Tx)
        → totalUTxO (applyTx tx s)
          ≡ applyTxToUTxO (isOurs s) tx (totalUTxO s)
```

Also, as discussed previously,
we require that the mapping between customers and addresses
remain unchanged:

```agda
      prop-listCustomers-applyTx
        : ∀ (s : WalletState) (tx : Tx)
        → listCustomers (applyTx tx s) ≡ listCustomers s
```

### Tracking incoming funds

The wallet tracks all addresses in `listCustomers`
whenever new blocks are incorporated into the wallet state.

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

Note that the customer deposit wallet does not support
delegation and reward accounts, and the `spent` value
can only be spent from transaction outputs.

The function `getCustomerHistory` allows users to detect incoming
transfers by observing the `received` value.

TODO: Expand on `summarize`.

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
      → PParams → WalletState → Maybe TxBody

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

