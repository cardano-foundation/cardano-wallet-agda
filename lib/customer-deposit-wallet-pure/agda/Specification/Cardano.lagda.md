# Specification: Cardano Types

This document provides a partial specification of
types related to the Cardano blockchain,
as needed by the Deposit Wallet.

```agda
module Specification.Cardano where
```

## Imports

```agda
open import Haskell.Prelude

import Specification.Cardano.Chain as ModChain
import Specification.Cardano.Value as ModValue
import Specification.Cardano.Tx as ModTx
```

## Signature

A signature records data types, operations,
and the properties that these operations should satisfy.

```agda
record Signature : Set₁ where
  field
```

We introduce new types

```agda
    CompactAddr : Set
    {{iEqCompactAddr}} : Eq CompactAddr

    PParams  : Set
```

and re-export the existing ones from `Specification.Cardano.*`

```agda
  field
    SigChain : ModChain.Signature

  field
    SigValue : ModValue.Signature
  open ModValue.Signature SigValue using (Value)

  field
    SigTx    : ModTx.Signature CompactAddr Value

  open ModChain.Signature SigChain public
  open ModValue.Signature SigValue public
  open ModTx.Signature SigTx public
```

For improved readability, we use the synonym

```agda
  Address = CompactAddr
```

to refer to addresses on Cardano.
