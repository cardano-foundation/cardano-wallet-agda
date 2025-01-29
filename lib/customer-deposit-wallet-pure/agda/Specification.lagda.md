# Specification: Customer Deposit Wallet

## Synopsis

🚧 DRAFT 2025-01-29

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
  * [Specification.Cardano.Chain](Specification/Cardano/Chain.lagda.md)
  — Type `Slot`.
  * [Specification.Cardano.Tx](Specification/Cardano/Tx.lagda.md)
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
* a specification `SigCardano` of Cardano-related concepts
that we need to formulate this specification, and
* a specification `SigWallet` of wallet-related concepts that are
  not the focus of this document.

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

      totalUTxO     : WalletState → UTxO
      getWalletSlot : WalletState → Slot
      applyTx       : Slot → Tx → WalletState → WalletState
      isOurs        : WalletState → Address → Bool

      getCustomerHistory
        : WalletState → Customer → List TxSummary

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
as a numerical index:

    Customer = Word31

The mapping between customers and addresses is maintained by
the following operations:

    deriveCustomerAddress : XPub → Customer → Address

    fromXPubAndMax        : XPub → Word31 → WalletState
    listCustomers         : WalletState → List (Customer × Address)

Here,

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
        : ∀ (w : WalletState)
        → isBijection (listCustomers w) ≡ True
```

The relation between `listCustomers` and `fromXPubAndMax`
is specified as follows:
First, the mapping precisely contains customers indices `0` to `cmax`:

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
        : ∀ (c : Customer)
            (xpub : XPub)
            (cmax : Word31)
            (addr : Address)
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

### Transactions and slots

Transactions are used to spend from or send funds to a wallet.
The type `Tx` represents a transaction.
The `WalletState` may keep a history of transactions.
In order to keep a history, we need a notion of time
— we use the type `Slot` to keep track of time,
as this type represents a time interval in which
one block can be forged.

In order to apply a `Tx` to the `WalletState`,
we specify a function

    applyTx : Slot → Tx → WalletState → WalletState

The first argument of this function is the `Slot`
of the block in which the transaction was included.

Transactions have to be applied in increasing `Slot` order.
For this reason, we also specify a function

    getWalletSlot : WalletState → Slot

that records the last `Slot` for which a transaction was
applied; this property is express as:

```agda
      prop-getWalletSlot-applyTx
        : ∀ (w    : WalletState)
            (slot : Slot)
            (tx   : Tx)
        → (getWalletSlot w <= slot) ≡ True
        → getWalletSlot (applyTx slot tx w)
          ≡ slot
```

An initial `WalletState` created with `fromXPubAndMax`
starts at genesis:

```agda
      prop-getWalletSlot-fromXPubAndMax
        : ∀ (xpub : XPub)
            (cmax : Customer)
        → getWalletSlot (fromXPubAndMax xpub cmax)
          ≡ genesis
```

For completeness, we decree that `applyTx` with a past `Slot`
are a no-op on the `WalletState`:

```agda
      prop-getWalletSlot-applyTx-past
        : ∀ (w    : WalletState)
            (slot : Slot)
            (tx   : Tx)
        → (getWalletSlot w <= slot) ≡ False
        → applyTx slot tx w
          ≡ w
```

Finally, we specify that the mapping between customers
and addresses is unchanged by transactions:

```agda
      prop-listCustomers-applyTx
        : ∀ (w    : WalletState)
            (slot : Slot)
            (tx   : Tx)
        → listCustomers (applyTx slot tx w)
          ≡ listCustomers w
```

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

The basics of `UTxO` management are as follows:
The total UTxO of the wallet that can be spent is given by the function

    totalUTxO : WalletState → UTxO

A transaction of type `Tx` may spend some outputs
and create new ones.
We assume that a function

    applyTxToUTxO : (Address → Bool) → Tx → UTxO → UTxO

applies the transaction to the `UTxO`.
Here, the first argument is a predicate that specifies which output
addresses of a transactions belong to the wallet.
For the Deposit Wallet,
the addresses belonging to the wallet are given by a function

    isOurs : WalletState → Address → Bool

Now, we extend the discussion to the entire `WalletState`:
First, we consider the predicate `isOurs`.
We require that all known customer addresses belong to the wallet

```agda
      prop-knownCustomerAddress-isOurs
        : ∀ (addr : Address)
            (w    : WalletState)
        → knownCustomerAddress addr w ≡ True
        → isOurs w addr ≡ True
```

However, there may be additional addresses belonging to the wallet,
in particular change addresses.

Second, we consider the application of a transaction.
We require that `applyTx`
is equivalent to `applyTxToUTxO` on the `totalUTxO`:

```agda
      prop-totalUTxO-applyTx
        : ∀ (slot : Slot)
            (w    : WalletState)
            (tx   : Tx)
        → (getWalletSlot w <= slot) ≡ True
        → totalUTxO (applyTx slot tx w)
          ≡ applyTxToUTxO (isOurs w) tx (totalUTxO w)
```

### Tracking incoming funds

The wallet tracks all addresses in `listCustomers`
whenever new blocks are incorporated into the wallet state.

The result of tracking is given by the operation

    getCustomerHistory : WalletState → Customer → List TxSummary

For a given customer,
this operation returns a list of transaction summaries.
A transaction summary (`TxSummary`)
reports the total `Value` spent or received
by the customer within a specific transaction.
The summary also includes the transaction id (`TxId`)
and the `Slot` at which the transaction was included in the blockchain.

    record ValueTransfer : Set where
      field
        spent    : Value
        received : Value

    open ValueTransfer

    TxSummary : Set
    TxSummary = Slot × TxId × ValueTransfer

Note that the deposit wallet does not support
delegation and reward accounts
— the `spent` field only records value spent from transaction
outputs.

The main purpose of the function `getCustomerHistory` is to
track the origin of incoming funds.
When a transactions makes a payment to an `address`
that belongs to a known customer `c`,
`customerAddress c ≡ Just address`,
a transaction summary with the corresponding transaction id
will show up in the result of `getCustomerHistory`
for the customer `c`.
This summary will record the total value that this customer
`received` in this transaction.

Note that the `spent` field in the `TxSummary` is for information only
— the deposit wallet does not distinguish customers when spending,
funds are taken out from customer addresses at random.
See the discussion of `createPayment` in a later section.

In order to specify the behavior of `getCustomerHistory`
more precisely,
we assume two functions

    spentTx    : Address → Tx → UTxO → Value
    receivedTx : Address → Tx → Value

which total the value spend, respectively received,
at a given address when a transaction is applied to a `UTxO`.
These functions are from
[Specification.Wallet.UTxO](./Specification/Wallet/UTxO.lagda.md).
We group them in a function

```agda
    summarizeTx : Address → Tx → UTxO → ValueTransfer
    summarizeTx addr tx u = record
      { spent    = spentTx addr tx u
      ; received = receivedTx addr tx
      }
```

Now, we require that applying a transaction to the
wallet state will add the summary of this transaction to
`getCustomerHistory`:

```agda
    field
      prop-getCustomerHistory-applyTx
        : ∀ (w : WalletState)
            (c : Customer)
            (address : Address)
            (tx : Tx)
            (slot : Slot)
        → (c , address) ∈ listCustomers w
        → (getWalletSlot w <= slot) ≡ True
        → getCustomerHistory (applyTx slot tx w) c
          ≡ (slot , getTxId tx , summarizeTx address tx (totalUTxO w))
            ∷ getCustomerHistory w c
```

On the other hand,
customers that are not known will not be tracked:

```agda
      prop-getCustomerHistory-knownCustomer
        : ∀ (w : WalletState)
            (c : Customer)
        → knownCustomer c w ≡ False
        → getCustomerHistory w c
          ≡ []
```

Finally, a wallet that was just initialized does
not contain a history of transactions, yet:

```agda
      prop-getCustomerHistory-fromXPubAndMax
        : ∀ (xpub : XPub) (cmax : Customer) (c : Customer)
        → getCustomerHistory (fromXPubAndMax xpub cmax) c
          ≡ []
```

The above properties provide a specification of
tracking incoming funds via `getCustomerHistory`.
For larger transaction histories,
this function may not offer the best performance
— for example, it does not limit the list of transactions,
and we cannot query recent transactions by customers.
However, we only specify one function here,
because these other queries can be specified
in terms of the result of `getCustomerHistory` alone,
without further reference to the `WalletState`.

### Creating transactions

Finally, we expose an operation

    createPayment
      : List (Address × Value)
      → PParams → WalletState → Maybe TxBody

which constructs a transaction that sends given values to given addresses.
Here, `PParams` are protocol parameters needed for computation the fee to
include in the transaction.

First, as the main purpose of a wallet is to be able to send funds,
it would be most desirable to require that this function always **succeeds**
in creating a transaction provided that the wallet has **sufficient funds**.
Unfortunately, however, we do not yet have an implementation
where we can prove this property. This topic is discussed in

* [Specification.Wallet.Payment](Specification/Wallet/Payment.lagda.md)
TODO: Call this "Balance"

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
from any address listed in `listCustomers`.

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

This property is not guarantee for other wallets,
such as [cardano-wallet][].
Unfortunately, this led to a very expensive bug.

  [cardano-wallet]: https://github.com/cardano-foundation/cardano-wallet
