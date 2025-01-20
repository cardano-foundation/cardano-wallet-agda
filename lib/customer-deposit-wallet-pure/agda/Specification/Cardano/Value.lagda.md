# Specification: Value

This document provides a partial specification of the `Value` type,
as needed by the Deposit Wallet.

```agda
module Specification.Cardano.Value where
```

A `Value` represents monetary value.
It is a collection that contains both ADA and optionally custom assets.

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

We are concerned with a single type

```agda
    Value : Set
```

that supports the following operations:

```agda
    empty         : Value
    add           : Value → Value → Value
    largerOrEqual : Value → Value → Bool
```

and an equality test

```agda
    {{iEqValue}}  : Eq Value
```

The operation `add` sums up the monetary values
contained in the arguments.
This operation has `empty` as left- and right identity.

```agda
    prop-add-x-empty
      : ∀ (x : Value)
      → add x empty ≡ x
    
    prop-add-empty-x
      : ∀ (x : Value)
      → add empty x ≡ x
```

The operation is both associative and commutative:

```agda
    prop-add-assoc
      : ∀ (x y z : Value)
      → add (add x y) z ≡ add x (add y z)

    prop-add-sym
      : ∀ (x y : Value)
      → add x y ≡ add y x
```

The operation `largerOrEqual x y` returns `True`
whenever the value `x` constains as many or strictly more assets
— both ADA and custom assets — than the value `y`.

In particular, adding a third value will not change
the relation in size:

```agda
    prop-add-monotone
      : ∀ (x y z : Value)
      → largerOrEqual (add x z) (add y z)
        ≡ largerOrEqual x y
```
