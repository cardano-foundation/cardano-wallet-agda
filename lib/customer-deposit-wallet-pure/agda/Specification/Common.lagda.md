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
open import Haskell.Data.Maybe using (isJust) public
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

The predicate `isSubsequenceOf` records whether
the elements of one list are contained in the other list,
in sequence.

```agda
isSubsequenceOf : ∀ {a : Set} {{_ : Eq a}} → List a → List a → Bool
isSubsequenceOf [] _ = True
isSubsequenceOf _ [] = False
isSubsequenceOf (x ∷ xs) (y ∷ ys) =
    if x == y
    then isSubsequenceOf xs ys
    else isSubsequenceOf (x ∷ xs) ys
```

The function `nub` is missing from `agda2hs`:

```agda
nub : {{Eq a}} → List a → List a
nub [] = []
nub (x ∷ xs) = x ∷ filter (x /=_) (nub xs)
```

The function `delete` deletes the first occurence
of the item from the list.

```agda
delete : ⦃ Eq a ⦄ → a → List a → List a
delete _ []       = []
delete x (y ∷ ys) = if x == y then ys else y ∷ delete x ys
```

The operator `_\\_` is list difference.
In the result `xs \\ ys`,
the first occurrence of each element of `ys`
in turn (if any) has been removed from `@xs`.

```agda
_\\_ : ⦃ Eq a ⦄ → List a → List a → List a
_\\_ = foldl (flip delete)
```
