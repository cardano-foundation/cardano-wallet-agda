module Haskell.Prim.Alternative where

open import Haskell.Prim.Type -- temporary

open import Haskell.Prim
open import Haskell.Prim.Applicative
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe

--------------------------------------------------
-- Alternative class

-- ** base
record Alternative (f : Type → Type) : Type₁ where
  field
    empty : f a
    _<|>_ : f a → f a → f a
    overlap ⦃ super ⦄ : Applicative f

    -- We do not define `some` and `many` yet,
    -- because they yield infinite co-data!
    -- some : f a → f (List a)
    -- many : f a → f (List a)

-- ** export
open Alternative ⦃...⦄ public
{-# COMPILE AGDA2HS Alternative existing-class #-}

-- ** instances
instance
  iAlternativeList : Alternative List
  iAlternativeList .empty = []
  iAlternativeList ._<|>_ = _++_

  iAlternativeMaybe : Alternative Maybe
  iAlternativeMaybe .empty = Nothing
  iAlternativeMaybe ._<|>_ Nothing  my = my
  iAlternativeMaybe ._<|>_ (Just x) _  = Just x

instance postulate iAlternativeIO : Alternative IO

--------------------------------------------------
-- Helper functions

-- | Conditional failure of 'Alternative' computations.
--
-- Very useful in @do@ notation of a 'MonadPlus'.
guard : ⦃ Alternative f ⦄ → Bool → f ⊤
guard True  = pure tt
guard False = empty
