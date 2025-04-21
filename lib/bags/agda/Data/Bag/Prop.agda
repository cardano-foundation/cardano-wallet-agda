{-# OPTIONS --erasure --rewriting #-}

-- | Proofs on 'Bag'.
module Data.Bag.Prop where

open import Haskell.Prim.Type -- temporary

open import Haskell.Prelude hiding (lookup; null; map; filter)

open import Data.Bag.Core
open import Data.Bag.Def

open import Haskell.Prim.Alternative
open import Haskell.Prim.MonadPlus
open import Haskell.Law
open import Haskell.Law.Extensionality
open import Haskell.Law.Monad.Extra
open import Haskell.Law.MonadPlus
open import Haskell.Law.Num

import Haskell.Prim.List as List
import Haskell.Law.Monad as Monad
import Haskell.Law.Monoid as Monoid

import Data.Monoid.Morphism as Monoid
import Data.Monoid.Refinement as Monoid

------------------------------------------------------------------------------
-- Move out: Additional type of monad

record IsCommutativeMonad (m : Type → Type) ⦃ _ : Monad m ⦄ : Type₁ where
  field
    -- Different monadic actions commute
    prop-monad-sym : ∀ {a b : Type} (mx : m a) (my : m b) (mz : a → b → m c)
      → mx >>= (λ x → my >>= (λ y → mz x y))
        ≡ my >>= (λ y → mx >>= (λ x → mz x y))

------------------------------------------------------------------------------
-- Move out: Helper function for proofs on monads

cong-monad
  : ∀ ⦃ _ : Monad m ⦄ (mx : m a) (f g : a → m b)
  → (∀ x → f x ≡ g x)
  → (do x ← mx; f x) ≡ (do x ← mx; g x)
cong-monad mx f g eq = cong (mx >>=_) (ext eq)

{-----------------------------------------------------------------------------
    Properties
    size
------------------------------------------------------------------------------}
{- [Rewrite size]

The properties of 'size' follow automatically from the rewrite rules
for 'foldBag'.
-}

-- | A 'singleton' has @'size' = 1@.
prop-size-singleton : ∀ (x : a) → size (singleton x) ≡ 1
--
prop-size-singleton x = refl

-- | The empty 'Bag' has @'size' = 0@.
prop-size-mempty : ∀ {a} → size {a} mempty ≡ 0
--
prop-size-mempty = refl

-- | The union of 'Bags' adds their sizes.
prop-size-<> : ∀ (xs ys : Bag a) → size (xs <> ys) ≡ size xs + size ys
--
prop-size-<> xs ys = refl

{-----------------------------------------------------------------------------
    Properties
    functorial type classes
------------------------------------------------------------------------------}
-- | 'map'ping the identity function leaves the result unchanged.
prop-map-id : ∀ (xs : Bag a) → map id xs ≡ xs
-- 
prop-map-id xs = prop-foldBag-unique id Monoid.prop-morphism-id xs

-- | 'map'ping a composition of functions gives the composition.
prop-map-∘
  : ∀ (f : a → b) (g : b → c) (xs : Bag a)
  → map (g ∘ f) xs ≡ (map g ∘ map f) xs
--
prop-map-∘ f g =
    prop-Bag-equality lhs rhs lhs-homo rhs-homo (λ x → refl)
  where
    lhs = map (g ∘ f)
    rhs = map g ∘ map f

    lhs-homo : Monoid.IsHomomorphism lhs
    lhs-homo = prop-morphism-foldBag _

    @0 rhs-homo : Monoid.IsHomomorphism rhs
    rhs-homo =
      Monoid.prop-morphism-∘ (map f) (map g)
        (prop-morphism-foldBag _)
        (prop-morphism-foldBag _)

instance
  iLawfulFunctorBag : IsLawfulFunctor Bag
  iLawfulFunctorBag .identity = prop-map-id
  iLawfulFunctorBag .composition xs f g = prop-map-∘ f g xs

-- postulated for now, need universal property on `foldBag`
-- that can deal with predicates.
postulate instance
  iLawfulMonadBag : IsLawfulMonad Bag

instance
  iLawfulMonadPlusBag : IsLawfulMonadPlus Bag
  iLawfulMonadPlusBag .mplus-mzero-x = Monoid.leftIdentity
  iLawfulMonadPlusBag .mplus-x-mzero = Monoid.rightIdentity
  iLawfulMonadPlusBag .mplus-assoc x y z = sym (Monoid.associativity x y z)
  iLawfulMonadPlusBag .mzero-bind k = refl
  iLawfulMonadPlusBag .bind-mzero = prop-foldBag-function-mempty

postulate instance
  iDistributiveMonadPlusBag : IsDistributiveMonadPlus Bag
  iCommutativeMonadBag      : IsCommutativeMonad Bag

{-----------------------------------------------------------------------------
    Properties
    fromList
------------------------------------------------------------------------------}
-- | 'fromList' maps single element lists to singleton
prop-fromList-[] : ∀ {a} → fromList {a} [] ≡ mempty
--
prop-fromList-[] = refl

-- | 'fromList' maps list concatenation to 'union' of 'Bag's.
prop-fromList-++
  : ∀ (xs ys : List a) 
  → fromList (xs ++ ys) ≡ fromList xs <> fromList ys
--
prop-fromList-++ [] ys = sym (Monoid.leftIdentity _)
prop-fromList-++ (x ∷ xs) ys
  rewrite ∷-++-assoc x xs ys
  rewrite prop-fromList-++ xs ys
  rewrite Monoid.associativity (singleton x) (fromList xs) (fromList ys)
  = refl

-- | 'fromList' preserves list length.
prop-size-fromList
  : ∀ (xs : List a)
  → size (fromList xs) ≡ length xs
--
prop-size-fromList [] = refl
prop-size-fromList (x ∷ xs) rewrite prop-size-fromList xs = refl

-- | 'fromList' maps 'Data.List.filter' to 'filter'.
prop-fromList-filter
  : ∀ (p : a → Bool) (xs : List a) 
  → fromList (List.filter p xs) ≡ filter p (fromList xs)
--
prop-fromList-filter p [] = refl
prop-fromList-filter p (x ∷ xs)
  with p x
... | False
    rewrite Monoid.leftIdentity (filter p (fromList xs))
    = prop-fromList-filter p xs
... | True
    rewrite prop-fromList-filter p xs
    = refl

{-----------------------------------------------------------------------------
    Properties
    Homomorphisms
------------------------------------------------------------------------------}
-- | 'size' is a monoid homomorphism.
prop-morphism-size
  : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ ⦃ MonoidSum ⦄ size
--
prop-morphism-size = prop-morphism-foldBag ⦃ Monoid.CommutativeSum ⦄ _

-- | 'fromList' is a monoid homomorphism.
prop-morphism-fromList
  : Monoid.IsHomomorphism (fromList {a})
--
prop-morphism-fromList =
  Monoid.MkIsHomomorphism prop-fromList-[] prop-fromList-++

-- | 'filter' is a monoid homomorphism.
prop-morphism-filter
  : ∀ (p : a → Bool) → Monoid.IsHomomorphism (filter p)
--
prop-morphism-filter p = prop-morphism-foldBag _

-- | 'null' is a monoid homomorphism.
prop-morphism-null
  : Monoid.IsHomomorphism ⦃ iMonoidBag {a} ⦄ ⦃ MonoidConj ⦄ null
--
prop-morphism-null = prop-morphism-foldBag ⦃ Monoid.CommutativeConj ⦄ _

-- | 'cartesianProduct' is a monoid homomorphism in its first argument.
prop-morphism-cartesianProduct-1
  : ∀ (ys : Bag b)
  → Monoid.IsHomomorphism (λ xs → cartesianProduct {a} {b} xs ys)
--
prop-morphism-cartesianProduct-1 ys = prop-morphism-foldBag _

-- | 'cartesianProduct' is a monoid homomorphism in its second argument.
prop-morphism-cartesianProduct-2
  : ∀ (xs : Bag a)
  → Monoid.IsHomomorphism (λ (ys : Bag b) → cartesianProduct {a} {b} xs ys)
--
prop-morphism-cartesianProduct-2 xs .Monoid.homo-mempty =
  prop-foldBag-function-mempty xs
prop-morphism-cartesianProduct-2 xs .Monoid.homo-<> ys1 ys2 =
  prop-foldBag-function-<> _ _ xs

-- | 'equijoin' is a monoid homomorphism in its first argument.
prop-morphism-equijoin-1
  : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (ys : Bag b)
  → Monoid.IsHomomorphism (λ xs → equijoin f g xs ys)
--
prop-morphism-equijoin-1 f g ys = prop-morphism-foldBag _

-- | 'equijoin' is a monoid homomorphism in its second argument.
prop-morphism-equijoin-2
  : ∀ {k} ⦃ _ : Eq k ⦄ (f : a → k) (g : b → k) (xs : Bag a)
  → Monoid.IsHomomorphism (λ ys → equijoin f g xs ys)
--
prop-morphism-equijoin-2 f g xs .Monoid.homo-mempty =
  prop-foldBag-function-mempty xs
prop-morphism-equijoin-2 f g xs .Monoid.homo-<> x y =
  prop-foldBag-function-<> _ _ xs

{-----------------------------------------------------------------------------
    Properties
    cartesianProduct
------------------------------------------------------------------------------}
-- | A 'cartesianProduct' is empty if and only if both arguments are empty.
postulate
 prop-null-cartesianProduct
  : ∀ (xs : Bag a) (ys : Bag b)
  → null (cartesianProduct xs ys) ≡ (null xs || null ys)
--
{-
prop-null-cartesianProduct =
    prop-Bag-equality-2 lhs rhs
      (λ xs → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-2 xs) prop-morphism-null)
      ?
      (λ ys → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-1 ys) prop-morphism-null)
      ?
      eq-singleton
  where 
    lhs = λ xs ys → null (cartesianProduct xs ys)
    rhs = λ xs ys → (null xs || null ys)
    eq-singleton
      : ∀ x y → lhs (singleton x) (singleton y) ≡ rhs (singleton x) (singleton y)
    eq-singleton x y = ?
-}

{-----------------------------------------------------------------------------
    Properties
    filter
------------------------------------------------------------------------------}
-- | Independent filters promote through cartesian product.
prop-filter-cartesianProduct
  : ∀ (p : a → Bool) (q : b → Bool) (xs : Bag a) (ys : Bag b)
  → filter (λ xy → p (fst xy) && q (snd xy)) (cartesianProduct xs ys)
    ≡ cartesianProduct (filter p xs) (filter q ys)
--
prop-filter-cartesianProduct p q =
    prop-Bag-equality-2 lhs rhs
      (λ xs → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-2 xs) (prop-morphism-filter r))
      (λ xs → Monoid.prop-morphism-∘ _ _ (prop-morphism-filter q) (prop-morphism-cartesianProduct-2 (filter p xs)))
      (λ ys → Monoid.prop-morphism-∘ _ _ (prop-morphism-cartesianProduct-1 ys) (prop-morphism-filter r))
      (λ ys → Monoid.prop-morphism-∘ _ _ (prop-morphism-filter p) (prop-morphism-cartesianProduct-1 (filter q ys)))
      eq-singleton
  where 
    r   = λ xy → p (fst xy) && q (snd xy)
    lhs = λ xs ys → filter r (cartesianProduct xs ys)
    rhs = λ xs ys → cartesianProduct (filter p xs) (filter q ys)
    eq-singleton
      : ∀ x y → lhs (singleton x) (singleton y) ≡ rhs (singleton x) (singleton y)
    eq-singleton x y
      with p x | q y
    ... | True  | True  = refl
    ... | True  | False = refl
    ... | False | True  = refl
    ... | False | False = refl
