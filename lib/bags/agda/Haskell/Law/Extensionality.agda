module Haskell.Law.Extensionality where

open import Haskell.Prim

--------------------------------------------------
-- Move out: Function extensionality

postulate
  ext : ∀ {f g : a → b} → (∀ x → f x ≡ g x) → f ≡ g

-- | Convenience:
-- Function extensionality for functions with two arguments
ext₂
  : ∀ {f g : a → b → c}
  → (∀ (x : a) (y : b) → f x y ≡ g x y) → f ≡ g
ext₂ eq = ext (λ x → ext (eq x))
