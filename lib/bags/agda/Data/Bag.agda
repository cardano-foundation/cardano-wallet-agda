{-# OPTIONS --erasure #-}

module Data.Bag
  {-|
  -- * Data
  -- ** Bag Type
  ; Bag
  -- ** Construction
  ; empty
  ; singleton
  ; fromList
  ; guard
  -- ** Query
  ; member
  -- ** Combine
  ; union
  -- ** Filter
  ; filter
    ; prop-filter-guard

  -- * Properties
  -} where

open import Haskell.Prelude hiding (filter)
open import Haskell.Law

{-----------------------------------------------------------------------------
    Type
------------------------------------------------------------------------------}
-- | A unordered, finite collection of items.
-- Items may appear more than once.
--
-- Bag is the free commutative monoid.
record Bag (a : Set) : Set where
  constructor MkBag
  field
    elements : List a

open Bag public

{-# COMPILE AGDA2HS Bag #-}

{-----------------------------------------------------------------------------
    Construction
------------------------------------------------------------------------------}

-- | The empty 'Bag'.
empty : Bag a
empty = MkBag []

{-# COMPILE AGDA2HS empty #-}

-- | 'Bag' with a single element.
singleton : a → Bag a
singleton x = MkBag (x ∷ [])

{-# COMPILE AGDA2HS singleton #-}

-- | Create a 'Bag' from a list of items.
fromList : List a → Bag a
fromList = MkBag

{-# COMPILE AGDA2HS fromList #-}

-- | Return a 'Bag' with one element if the condition is 'True',
-- and 'empty' if the condition is 'False'.
-- Very useful for @do@ notation.
--
-- From "Control.Monad".
guard : Bool → Bag ⊤
guard True = singleton tt
guard False = empty

{-# COMPILE AGDA2HS guard #-}

-- Special syntax for highlighting that an expression is a bag.
-- Escape sequences:
-- ⟅ = \(9
-- ⟆ = \)9
⟅_⟆ : Bag a → Bag a
⟅_⟆ x = x

{-----------------------------------------------------------------------------
    Query
------------------------------------------------------------------------------}
-- | Is the item in the 'Bag'?
member : ⦃ Eq a ⦄ → a → Bag a → Bool
member x (MkBag xs) = elem x xs

{-# COMPILE AGDA2HS member #-}

-- | Delete the first occurrence of an item from the list.
-- Return 'Nothing' if the element does not occur.
delete1 : ⦃ Eq a ⦄ → a → List a → Maybe (List a)
delete1 x [] = Nothing
delete1 x (y ∷ ys) = if x == y then Just ys else fmap (y ∷_) (delete1 x ys)

{-# COMPILE AGDA2HS delete1 #-}

-- | Two lists are equal as bags.
eqBag : ⦃ Eq a ⦄ →  List a → List a → Bool
eqBag []       []       = True
eqBag []       (y ∷ ys) = False
eqBag (x ∷ xs) ys'      = case delete1 x ys' of λ where
    (Just ys) → eqBag xs ys
    Nothing   → False

{-# COMPILE AGDA2HS eqBag #-}

instance
  iEqBag : ⦃ Eq a ⦄ → Eq (Bag a)
  iEqBag ._==_ (MkBag xs) (MkBag ys) = eqBag xs ys

{-# COMPILE AGDA2HS iEqBag derive #-}

postulate instance
  iLawfulEqBag : ⦃ _ : Eq a ⦄ → ⦃ IsLawfulEq a ⦄ → IsLawfulEq (Bag a)

instance
  iDefaultFunctorBag : DefaultFunctor Bag
  iDefaultFunctorBag .DefaultFunctor.fmap f (MkBag xs) = MkBag (fmap f xs)

  iFunctorBag : Functor Bag
  iFunctorBag = record {DefaultFunctor iDefaultFunctorBag}

  -- Not sure what is going on here, but using
  --   iDefaultApplicativeBag : DefaultApplicative Bag
  -- emits *two* definitions for `pure` and `<*>`.
  --
  -- Using an explicit `record` in `iApplicativeBag` yields
  -- triggers a bug in agda2hs / Agda:
  --   __IMPOSSIBLE__,
  --   called at src/full/Agda/TypeChecking/Telescope.hs:625:28
  --   in Agda-2.7.0-4AYHYh2TvbO6boiLogUmpv:Agda.TypeChecking.Telescope
  iApplicativeBag : Applicative Bag
  iApplicativeBag .pure = λ x → MkBag (pure x)
  iApplicativeBag ._<*>_ = λ fs xs → MkBag (elements fs <*> elements xs)
  iApplicativeBag ._<*_ = λ fs xs → MkBag (elements fs <* elements xs)
  iApplicativeBag ._*>_ = λ fs xs → MkBag (elements fs *> elements xs)

  iDefaultMonadBag : DefaultMonad Bag
  iDefaultMonadBag .DefaultMonad._>>=_ (MkBag m) f =
    MkBag (m >>= (elements ∘ f))

  iMonadBag : Monad Bag
  iMonadBag = record {DefaultMonad iDefaultMonadBag}

{-# COMPILE AGDA2HS iFunctorBag #-}
{-# COMPILE AGDA2HS iApplicativeBag #-}
{-# COMPILE AGDA2HS iMonadBag #-}

{-----------------------------------------------------------------------------
    Combine
------------------------------------------------------------------------------}
-- | The union of two 'Bag's contains all items from each of the 'Bag's.
--
-- 'union' is commutative.
union : Bag a → Bag a → Bag a
union (MkBag xs) (MkBag ys) = MkBag (xs <> ys)

{-# COMPILE AGDA2HS union #-}

instance
  iSemigroupBag : Semigroup (Bag a)
  iSemigroupBag ._<>_ = union

  iDefaultMonoidBag : DefaultMonoid (Bag a)
  iDefaultMonoidBag .DefaultMonoid.mempty = empty

  iMonoidBag : Monoid (Bag a)
  iMonoidBag = record{DefaultMonoid iDefaultMonoidBag}

{-# COMPILE AGDA2HS iSemigroupBag #-}
{-# COMPILE AGDA2HS iMonoidBag #-}

{-----------------------------------------------------------------------------
    Filter
------------------------------------------------------------------------------}
-- | Filter all elements that satisfy the predicate.
filter : (a → Bool) → Bag a → Bag a
filter = λ p xs → do
  x ← xs
  guard (p x)
  pure x

{-# COMPILE AGDA2HS filter #-}

-- | 'filter' can be written using @do@ notation with a 'guard'.
-- 
prop-filter-guard
  : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (p : a → Bool) (xs : Bag a)
  → (filter p xs
    == (do x ← xs; guard (p x); pure x)) ≡ True
--
prop-filter-guard p xs = equality' (filter p xs) _ refl

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- | 'Bag' is a commutative monad.
--
postulate
 prop-monad-sym
  : ∀ ⦃ _ : Eq a ⦄ (xs ys : Bag a)
  → ((do x ← xs; y ← ys; pure (x , y))
    == (do y ← ys; x ← xs; pure (x , y))) ≡ True

{-----------------------------------------------------------------------------
    Examples
------------------------------------------------------------------------------}

example0 : Bag Integer
example0 = fromList (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [])

example1 : Bag Integer
example1 = do
  x ← example0
  y ← example0
  guard (x == y)
  pure (x + y)
