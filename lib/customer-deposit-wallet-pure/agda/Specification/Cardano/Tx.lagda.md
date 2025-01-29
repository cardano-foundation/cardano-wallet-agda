# Specification: Transactions

This document provides a partial specification of the `Tx` type
and related types, as needed by the Deposit Wallet.

```agda
module Specification.Cardano.Tx where
```

A `Tx` represents a transaction.
A transactions creates transaction outputs
and spends previously created transaction outputs.

## Imports

```agda
open import Haskell.Prelude
open import Haskell.Reasoning
```

## Signature

A signature records data types, operations,
and the properties that these operations should satisfy.

```agda
record Signature (Address : Set) (Value : Set) : Set₁ where
  field
```

We are concerned with types

```agda
    TxBody : Set
    Tx     : Set
    TxId   : Set
```

that support the following operations:

```agda
    outputs : TxBody → List (Address × Value)
    getTxId : Tx → TxId
```
