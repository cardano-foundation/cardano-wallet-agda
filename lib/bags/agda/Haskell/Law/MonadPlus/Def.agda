module Haskell.Law.MonadPlus.Def where

open import Haskell.Prim.Type -- temporary

open import Haskell.Prim

open import Haskell.Prim.Alternative
open import Haskell.Prim.Applicative
open import Haskell.Prim.Functor
open import Haskell.Prim.Monad
open import Haskell.Prim.MonadPlus
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple

open import Haskell.Law.Equality
open import Haskell.Law.Monad
open import Haskell.Law.Monad.Extra
open import Haskell.Law.Monoid

--------------------------------------------------
-- IsLawfulMonadPlus

record IsLawfulMonadPlus (m : Type → Type) ⦃ i : MonadPlus m ⦄ : Type₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulMonad m

    mplus-mzero-x : ∀ (x : m a)     → mplus mzero x ≡ x
    mplus-x-mzero : ∀ (x : m a)     → mplus x mzero ≡ x
    mplus-assoc   : ∀ (x y z : m a) → mplus (mplus x y) z ≡ mplus x (mplus y z)

    mzero-bind : ∀ (k  : a → m b) → mzero >>= k ≡ mzero
    bind-mzero : ∀ (mx : m a)     → mx >>= (λ x → mzero) ≡ mzero {m} {b}

open IsLawfulMonadPlus ⦃ ... ⦄ public

-- convenient synonym
prop-mzero->>=
  : ∀ ⦃ _ : MonadPlus m ⦄ ⦃ _ : IsLawfulMonadPlus m ⦄
  → (k : a → m b) → mzero >>= k ≡ mzero
prop-mzero->>= = mzero-bind

prop-mzero->>
  : ∀ {a b} ⦃ _ : MonadPlus m ⦄ ⦃ _ : IsLawfulMonadPlus m ⦄
  → (my : m b) → mzero {m} {a} >> my ≡ mzero
prop-mzero->> {m} {a} my =
  begin
    (mzero {m} {a} >> my)
  ≡⟨ prop->>->>= _ _ ⟩
    (mzero {m} {a} >>= (λ x → my))
  ≡⟨ prop-mzero->>= _ ⟩
    mzero
  ∎

--------------------------------------------------
-- IsDistributiveMonadPlus

record IsDistributiveMonadPlus (m : Type → Type) ⦃ _ : MonadPlus m ⦄ : Type₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulMonadPlus m

    mplus-bind : ∀ {a b} (x y : m a) (k : a → m b)
      →  mplus x y >>= k  ≡  mplus (x >>= k) (y >>= k)

open IsDistributiveMonadPlus ⦃ ... ⦄ public
