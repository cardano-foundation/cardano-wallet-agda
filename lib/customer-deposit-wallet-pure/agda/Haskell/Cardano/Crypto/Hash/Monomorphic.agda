{-# OPTIONS --erasure #-}

module Haskell.Cardano.Crypto.Hash.Monomorphic where

open import Haskell.Prelude

open import Haskell.Data.ByteString using
    ( ByteString
    )

{- Note [HashInjective]

Cryptographic hash functions are injective !?

The following postulate is the most important postulate about
cryptographic Hash functions — we postulate that they are *injective*,
i.e. that the hash values of two distinct inputs do not collide.

Of course, any practical hash function that maps arbitrary ByteStrings to
a finite codomain cannot be injective — there are not enough elements
in the codomain to distinguish the infinite number of possible elements
of the domain.
So, this postulate is actually *inconsistent* when applied to actual
hash functions.

However!
We take care to allow an infinite codomain for the hash
function. Thus, there exists at least one "hash" function which
is injective — the "trivial hash" that maps the input to a complete
encoding of itself, discarding no information.
Hence, the postulate is independent of Agda
— it is true for some hash functions, but not for others.

As long as we hide the implementation details of the specific
Hash algorithm, we can pretend that we work in a model
where the postulate is true.

TODO: Find an even better to do this postulate in Agda.
This postulate is generally assumed about cryptographic Hash functions,
but I would like to pinpoint the fact that it's not possible
to derive a contradiction in Agda.
-}

{-----------------------------------------------------------------------------
    Blake2b
------------------------------------------------------------------------------}

postulate
  blake2b'224 : ByteString → ByteString
  blake2b'256 : ByteString → ByteString

  prop-blake2b'224-injective
    : ∀ (x y : ByteString)
    → blake2b'224 x ≡ blake2b'224 y
    → x ≡ y

  prop-blake2b'256-injective
    : ∀ (x y : ByteString)
    → blake2b'256 x ≡ blake2b'256 y
    → x ≡ y
