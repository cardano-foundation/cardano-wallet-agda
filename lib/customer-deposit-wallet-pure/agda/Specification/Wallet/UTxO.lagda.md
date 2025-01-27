# Specification: UTxO

This document provides an entrypoint to the specification
of UTxO-style accounting for cryptocurrency wallets.

This topic is discussed in-depth in

* D. Coutts and E. de Vries. [Formal specification for a Cardano wallet][wallet]. (2018)

In light of this prior art, the specification of the Deposit Wallet
focuses on other topics; here, we just collect the most basic notions.

  [wallet]: https://iohk.io/en/research/library/papers/formal-specification-for-a-cardano-wallet/

```agda
module Specification.Wallet.UTxO where
```

## Imports

```agda
open import Haskell.Prelude

import Specification.Cardano
```

## Signature

A signature records data types, operations,
and the properties that these operations should satisfy.

```agda
record
  Signature
    (SigCardano : Specification.Cardano.Signature)
    : Set₁
  where
  open Specification.Cardano.Signature SigCardano
  field
```

We introduce new types

```agda
    UTxO : Set
```

and functions

```agda
    balance : UTxO → Value

    applyTxToUTxO : (Address → Bool) → Tx → UTxO → UTxO

    spentTx    : Address → Tx → UTxO → Value
    receivedTx : Address → Tx → Value
```

The function `balance` computes the total value contained in the
unspent outputs.

The function `applyTxToUTxO isOurs tx utxo` applies the given
transaction `tx` to the unspent transction outputs in `utxo`.
The predicate `isOurs` indicates whether the address of an output
belongs to the wallet, typically because the wallet owner knows
the corresponding signing key.
Only those outputs that satisfy `isOurs` are included in the
updated `UTxO`.

The function `spentTx` computes the `Value`
spent by the transaction on the given address
— without accounting for received value.

In turn, the function `receivedTx` computes the `Value`
received by the transaction on the given address
— without accounting for spent value.

At this level of detail, we cannot formulate any properties
— we would need a definition of `Tx` for that purpose.
