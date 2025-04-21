{-# OPTIONS --erasure --rewriting #-}

-- | Operations on 'Bag' defined in terms of the axiomatization.
module Data.Bag.Def where

open import Haskell.Prim
open import Haskell.Prim.Alternative
open import Haskell.Prim.Applicative
open import Haskell.Prim.Eq
open import Haskell.Prim.Foldable using (foldMap)
open import Haskell.Prim.Functor
open import Haskell.Prim.Int
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monad
open import Haskell.Prim.MonadPlus
open import Haskell.Prim.Monoid
open import Haskell.Prim.Num
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple

open import Haskell.Law.Function
open import Haskell.Law.Num

open import Data.Bag.Core
import Data.Monoid.Refinement as Monoid

{-----------------------------------------------------------------------------
    Operations
    basic
------------------------------------------------------------------------------}
-- | Test whether the 'Bag' is empty.
null : Bag a → Bool
null = foldBag {{Monoid.CommutativeConj}} (λ _ → False)

-- | Union of all items from the two arguments.
-- Synonym for '(<>)'.
union : Bag a → Bag a → Bag a
union = _<>_

-- | A 'Bag' that may contain an element.
fromMaybe : Maybe a → Bag a
fromMaybe Nothing  = mempty
fromMaybe (Just x) = singleton x

-- | Number of items in the Bag.
size : Bag a → Int
size = foldBag {{Monoid.CommutativeSum}} (λ _ → 1)

-- | Apply a function to all elements in the 'Bag'
-- and take the union of the results.
concatMap : (a → Bag b) → Bag a → Bag b
concatMap = foldBag

-- | Apply a function to all elements in the 'Bag'.
map : (a → b) → Bag a → Bag b
map f = concatMap (singleton ∘ f)

-- | Obtain a 'Bag' with the same items as a given list.
fromList : List a → Bag a
fromList = foldMap singleton

{-----------------------------------------------------------------------------
    Operations
    functorial type classes
------------------------------------------------------------------------------}
instance
  iDefaultFunctorBag : DefaultFunctor Bag
  iDefaultFunctorBag .DefaultFunctor.fmap = map

  iFunctorBag : Functor Bag
  iFunctorBag = record{DefaultFunctor iDefaultFunctorBag}

  iDefaultApplicativeBag : DefaultApplicative Bag
  iDefaultApplicativeBag .DefaultApplicative.pure = singleton
  iDefaultApplicativeBag .DefaultApplicative._<*>_ fs xs =
    concatMap (λ f → map f xs) fs

  iApplicativeBag : Applicative Bag
  iApplicativeBag = record{DefaultApplicative iDefaultApplicativeBag}

  iDefaultMonadBag : DefaultMonad Bag
  iDefaultMonadBag .DefaultMonad._>>=_ = flip concatMap

  iMonadBag : Monad Bag
  iMonadBag = record{DefaultMonad iDefaultMonadBag}

  iAlternativeBag : Alternative Bag
  iAlternativeBag .Alternative.empty = mempty
  iAlternativeBag .Alternative._<|>_ = _<>_

  iMonadPlusBag : MonadPlus Bag
  iMonadPlusBag = record { unique-applicative = refl }

{-----------------------------------------------------------------------------
    Operations
    Definitions using do-notation
------------------------------------------------------------------------------}
-- | Keep only those elements that satisfy a predicate.
filter : (a → Bool) → Bag a → Bag a
filter p xs = do x ← xs; guard (p x); pure x

-- | Count the number of times that an item is contained in the 'Bag'.
count : ⦃ Eq a ⦄ → a → Bag a → Int
count x = size ∘ filter (x ==_)

-- | Check whether an item is contained in the 'Bag' at least once.
member : ⦃ Eq a ⦄ → a → Bag a → Bool
member x ys = 0 < count x ys

-- | 'Bag' containing all possible pairs of items.
cartesianProduct : Bag a → Bag b → Bag (a × b)
cartesianProduct xs ys = do x ← xs; y ← ys; pure (x , y)

-- | 'Bag' containing all possible pairs of items where
-- the functions yield the same result.
equijoin
    : ∀ {k} ⦃ _ : Eq k ⦄
    → (a → k) → (b → k) → Bag a → Bag b → Bag (a × b)
equijoin f g xs ys = do x ← xs; y ← ys; guard (f x == g y); pure (x , y)
