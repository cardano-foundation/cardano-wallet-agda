module Haskell.Prim.MonadPlus where

open import Haskell.Prim.Type -- temporary

open import Haskell.Prim
open import Haskell.Prim.Alternative
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monad

--------------------------------------------------
-- MonadPlus

-- ** base
record MonadPlus (m : Type → Type) : Type₁ where
  field
    overlap ⦃ alternative ⦄ : Alternative m
    overlap ⦃ monad ⦄ : Monad m

    -- The 'Applicative' instances from the two superclasses are the same.
    -- This is required for global uniqueness of type classes in Haskell.
    unique-applicative : alternative .Alternative.super ≡ monad .Monad.super

-- Note: To infer that member functions such as `pure` are equal, using
-- `cong Applicative.pure unique-applicative`
-- may not type check, as `cong` does not work with `Type₁`.
-- Provide a different definition of `cong` to make this work.

-- ** defaults
--
-- In order to simplify proofs, we impose the laws
--   mzero ≡ empty
--   mplus ≡ _<|>_
-- by definition.

mzero : ⦃ MonadPlus m ⦄ → m a
mzero = empty

mplus : ⦃ MonadPlus m ⦄ → m a → m a → m a
mplus = _<|>_

-- ** export
open MonadPlus ⦃...⦄ public
{-# COMPILE AGDA2HS MonadPlus existing-class #-}

-- ** instances
instance
  iMonadPlusList : MonadPlus List
  iMonadPlusList = record { unique-applicative = refl }

  iMonadPlusMaybe : MonadPlus Maybe
  iMonadPlusMaybe = record { unique-applicative = refl }

instance postulate iMonadPlusIO : MonadPlus IO
