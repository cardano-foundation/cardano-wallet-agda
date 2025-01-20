# Specification: Common concepts

This document introduces common concepts used during the specification.

```agda
module Specification.Common where
```

## Imports

We rely on common Haskell types, such as pairs, lists, …

```agda
open import Haskell.Prelude
open import Haskell.Reasoning
```

## Additions

However, we also require a few convenience concepts
not covered by the imports above.

The logical combinator "if and only if"

```agda
_⇔_ : Set → Set → Set
x ⇔ y = (x → y) ⋀ (y → x)
```

The predicate `_∈_` records whether an item is an element of a list

```agda
_∈_ : ∀ {a : Set} {{_ : Eq a}} → a → List a → Set
x ∈ xs = elem x xs ≡ True
```

The predicate `isSubsetOf` records whether all elements of
one list are also contained in the other list.

```agda
isSubsetOf : ∀ {a : Set} {{_ : Eq a}} → List a → List a → Bool
isSubsetOf xs ys = all (λ x → elem x ys) xs
```
