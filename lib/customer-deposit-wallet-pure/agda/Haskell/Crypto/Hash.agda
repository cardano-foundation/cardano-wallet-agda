{-# OPTIONS --erasure #-}

-- Inspired by "cryptonite" Crypto.Hash
module Haskell.Crypto.Hash
    {-
    ; Digest
      ; encodeDigest 
    ; HashAlgorithm
      ; HashAlgorithm.hash
      ; HashAlgorithm.prop-hash-injective
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.ByteString using
    ( ByteString
    )

{-----------------------------------------------------------------------------
    Hash algorithms
------------------------------------------------------------------------------}

data Digest (alg : Set) : Set where
  DigestC : Nat → Digest alg

-- | Encode a 'Digest' as a natural number.
encodeDigest : ∀ {alg} → Digest alg → Nat
encodeDigest (DigestC n) = n

{-# COMPILE AGDA2HS Digest #-}
{-# COMPILE AGDA2HS encodeDigest #-}

--
prop-encodeDigest-injective
  : ∀ {alg}
      (x y : Digest alg)
  → encodeDigest x ≡ encodeDigest y
  → x ≡ y
--
prop-encodeDigest-injective (DigestC a) (DigestC b) refl = refl

record HashAlgorithm (alg : Set) : Set where
  field
    hash : ByteString → Digest alg

    -- See Note [HashInjective]
    @0 prop-hash-injective
      : ∀ (x y : ByteString)
      → hash x ≡ hash y
      → x ≡ y

open HashAlgorithm ⦃ ... ⦄ public

{-# COMPILE AGDA2HS HashAlgorithm class #-}

{- Note [HashInjective]

Cryptographic hash functions are injective !?

The following postulate is the most important postulate about
cryptographic Hash functions — that they are *injective*,
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
    Trivial "hash"
------------------------------------------------------------------------------}
data TrivialHash : Set where
  TrivialHashC : TrivialHash

abstract
  instance
    iTrivialHashAlgorithm : HashAlgorithm TrivialHash
    iTrivialHashAlgorithm = record
        { hash = λ _ → DigestC 0 -- TODO: Ouch.
        ; prop-hash-injective = inj
        }
      where
        postulate inj : _


{-# COMPILE AGDA2HS TrivialHash #-}
{-# COMPILE AGDA2HS iTrivialHashAlgorithm #-}
