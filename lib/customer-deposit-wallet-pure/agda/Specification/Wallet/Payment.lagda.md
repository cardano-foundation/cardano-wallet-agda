# Specification: Creating Payments Success

This document discusses the success conditions of a function
`createPayment` that creates a payment by
selecting transaction outputs from a `UTxO`.

## Imports

```agda
open import Haskell.Prelude
open import Haskell.Reasoning
open import Haskell.Data.Maybe using (isJust)

import Specification.Cardano.Value

module
  Specification.Wallet.Payment
    (ValueSig : Specification.Cardano.Value.Signature)
  where

open Specification.Cardano.Value.Signature ValueSig
```

## Signature

A signature records data types, operations,
and the properties that these operations should satisfy.

```agda
record Signature : Set₁ where
  field
```

Besides `Value`, we assume several other data types and functions

```agda
    Address : Set
    PParams : Set
    Tx      : Set
    UTxO    : Set

    balance : UTxO → Value
```

### `createPayment`

The main purpose of a wallet is to send and receive
funds to other people.

Given a list of monetary `Value` and `Address` to send them to,
the function

```agda
    createPayment
      : List (Address × Value)
      → PParams → UTxO → Maybe Tx
```

creates a transaction by selecting transaction outputs from
the curently available `UTxO` of the wallet.

The main property desired of this function is that it always
succeeds in creating a transaction as long as the wallet has
sufficient funds.

One way of formalizing this property would be as follows:
For simplicity, let us assume that there is a maximum fee
which covers any transaction:

```agda
    maxFee : PParams → Value
```

Then, the idea is that we can always create a transaction,
as long as the available `UTxO` exceed the value to be paid out
plus the maximum fee: 

```agda
  totalValue : List (Address × Value) → Value
  totalValue = foldr add empty ∘ map snd

  field
    prop-createPayment-success
      : ∀ (utxo : UTxO)
          (pp : PParams)
          (destinations : List (Address × Value))
      → largerOrEqual
          (balance utxo)
          (add (totalValue destinations) (maxFee pp))
        ≡ True
      → isJust (createPayment destinations pp utxo) ≡ True
```

Unfortunately however, this property cannot hold as written
on Cardano.
Besides this condition of insufficient funds,
there are other reasons for failure:

* Wallet UTxO is poor
  * Few UTxO which are too close to minimum ADA quantity
  * UTxO with too many native assets
* Destinations are poor
  * `Value` does not carry minimum ADA quantity
  * `Value` size too large (native assets, `Datum`, …)
* Combination of both:
  * Too many UTxO with small ADA amount
    that we need to cover a large `Value` payment.
    Example: "Have 1 million x 1 ADA coins, want to send 1 x 1'000'000 ADA coin."

We currently do not know a formal property
that guarantees success of `createPayment`,
but also admits an implementation,
as this requires handling the above potential failure cases.
