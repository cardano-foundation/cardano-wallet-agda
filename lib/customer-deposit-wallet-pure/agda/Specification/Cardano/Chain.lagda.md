# Specification: Chain

This document provides a partial specification of
types related to identifying points on the blockchain,
as needed by the Deposit Wallet.

```agda
module Specification.Cardano.Chain where
```

## Imports

```agda
open import Haskell.Prelude
open import Haskell.Reasoning
```

## Signature

A signature records data types, operations,
and the properties that these operations should satisfy.

```agda
record Signature : Set₁ where
  field
```

The type

```agda
    Slot : Set
```

that represents time intervals in which one block
can be forged.

The type

```agda
    ChainPoint : Set
```

represents a point on the blockchain, i.e. the unique hash
and `Slot` of a block that has been forged.

The `Slot` type supports equality and comparison:

```agda
    instance
      iEqSlot  : Eq Slot
      iOrdSlot : Ord Slot
```

This comparison is a total order:

```agda
      iIsLawfulOrdSlot : IsLawfulOrd Slot {{iOrdSlot}}
```

The smallest `Slot` is called `genesis`,
which technically does not correspond to a block,
but represents the genesis parameters of the blockchain.

```agda
    genesis : Slot

    prop-genesis-<=
      : ∀ (x : Slot)
      → (_<=_ {{iOrdSlot}} genesis x) ≡ True
```

The `ChainPoint` type supports an operation

```agda
    slotFromChainPoint : ChainPoint → Slot
```

that retrieves the `Slot` of the block that is referenced
by the `ChainPoint`.
