
-- Extra properties that should be in Control.Monad

module Haskell.Law.Monad.Extra where

open import Haskell.Prim
open import Haskell.Prim.Applicative
open import Haskell.Prim.Monad
open import Haskell.Law.Equality
open import Haskell.Law.Monad

--------------------------------------------------
-- Missing properties

-- The missing properties below seem to be a general
-- issue with type class defaults —
-- strictly speaking, we would need to supply proofs
-- that they are equivalent to the default definition.

-- This property should be enforced.
postulate
 prop-return-pure
  : ∀ ⦃ _ : Monad m ⦄ ⦃ _ : IsLawfulMonad m ⦄
  → ∀ (x : a) → return {m} x ≡ pure x

-- At the moment, the following property cannot be proven
-- from IsLawfulMonad and IsLawfulApplicative alone!
postulate
  prop->>->>=
    : ∀ ⦃ _ : Monad m ⦄ ⦃ _ : IsLawfulMonad m ⦄
    → (mx : m a) (my : @0 ⦃ a ⦄ → m b)
    → mx >> my ≡ mx >>= (λ x → my ⦃ x ⦄)

--------------------------------------------------
-- Monad laws,
-- formulated in terms of 'do' notation.

-- | @do@ notation: Associativity of monadic bind.
prop-do-assoc
  : ∀ ⦃ _ : Monad m ⦄ ⦃ _ : IsLawfulMonad m ⦄
  → ∀ {a b c} (mx : m a) (my : a → m b) (mz : b → m c)
  → (do y ← (do x ← mx; my x); mz y)
    ≡ (do x ← mx; y ← my x; mz y)
--
prop-do-assoc mx my mz = sym (associativity mx my mz)

-- | @do@ notation: 'return'ing a value has no side effect.
prop-do-return-k
  : ∀ ⦃ _ : Monad m ⦄ ⦃ _ : IsLawfulMonad m ⦄
  → ∀ {a b} (x : a) (k : a → m b)
  → (do x' ← return x; k x')
    ≡ (do k x)
--
prop-do-return-k = leftIdentity

-- | @do@ notation: 'return'ing the previous value is superfluous.
prop-do-mx-return
  : ∀ ⦃ _ : Monad m ⦄ ⦃ _ : IsLawfulMonad m ⦄
  → ∀ {a} (mx : m a)
  → (do x ← mx; return x)
    ≡ (do mx)
--
prop-do-mx-return = rightIdentity
