-- | Monoid morphisms
module Data.Monoid.Morphism where

open import Haskell.Prim.Type -- temporary

open import Haskell.Prim
open import Haskell.Prim.Monoid

open import Haskell.Law

-------------------------------------------------------------------------------
-- Monoid Homomorphisms

record IsHomomorphism ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄ (f : a → b)
    : Type where
  constructor MkIsHomomorphism
  field
    homo-mempty : f mempty ≡ mempty
    homo-<>     : ∀ x y → f (x <> y) ≡ f x <> f y

open IsHomomorphism public

-------------------------------------------------------------------------------
-- Properties

-- | The identity map is a homomorphism.
prop-morphism-id : ∀ ⦃ _ : Monoid a ⦄ → IsHomomorphism (id {a})
--
prop-morphism-id = MkIsHomomorphism refl (λ x y → refl)

-- | The composition of two homomorphisms is again a homomorphism.
prop-morphism-∘
  : ∀ ⦃ _ : Monoid a ⦄ ⦃ _ : Monoid b ⦄ ⦃ _ : Monoid c ⦄
      (f : a → b) (g : b → c)
  → IsHomomorphism f → IsHomomorphism g → IsHomomorphism (g ∘ f)
--
prop-morphism-∘ f g prop-f prop-g = record
  { homo-mempty =
    trans (cong g (homo-mempty prop-f)) (homo-mempty prop-g)
  ; homo-<> = λ x y →
    trans (cong g (homo-<> prop-f x y)) (homo-<> prop-g (f x) (f y))
  }
