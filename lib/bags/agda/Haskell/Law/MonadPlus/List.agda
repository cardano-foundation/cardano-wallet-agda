module Haskell.Law.MonadPlus.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Monad
open import Haskell.Prim.MonadPlus

open import Haskell.Law.MonadPlus.Def

open import Haskell.Law.Equality
open import Haskell.Law.List
open import Haskell.Law.Monad.List

--------------------------------------------------
-- IsLawfulMonadPlus

private
  prop-bind-mzero : ∀ (xs : List a) → xs >>= (λ x → mzero) ≡ mzero {List} {b}
  prop-bind-mzero [] = refl
  prop-bind-mzero {a} {b} (x ∷ xs)
    rewrite prop-bind-mzero {a} {b} xs
    = refl

instance
  iLawfulMonadPlusList : IsLawfulMonadPlus List
  iLawfulMonadPlusList .mplus-mzero-x = []-++
  iLawfulMonadPlusList .mplus-x-mzero = ++-[]
  iLawfulMonadPlusList .mplus-assoc = ++-assoc
  iLawfulMonadPlusList .mzero-bind k = refl
  iLawfulMonadPlusList .bind-mzero = prop-bind-mzero

--------------------------------------------------
-- IsDistributiveMonadPlus

instance
  iDistributiveMonadPlusList : IsDistributiveMonadPlus List
  iDistributiveMonadPlusList .mplus-bind x y k =
    sym (concatMap-++-distr x y k)
