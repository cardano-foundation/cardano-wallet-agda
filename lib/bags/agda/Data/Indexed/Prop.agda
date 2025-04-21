{-# OPTIONS --erasure --rewriting --irrelevant-projections #-}

-- | Proofs about indexed 'Table's.
module Data.Indexed.Prop where

open import Haskell.Prelude hiding (filter; lookup; null)

open import Data.Indexed.Def

open import Data.Bag using (Bag)
import Data.Bag as Bag
open import Data.Map using (Map)
import Data.Map as Map
import Data.Map.Prop.Extra as Map
open import Data.Map.Prop.Extra using (prop-if-apply)

open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Extensionality

import Haskell.Law.Monoid as Monoid
import Data.Monoid.Morphism as Monoid
import Data.Monoid.Refinement as Monoid

{-----------------------------------------------------------------------------
    Properties
    Singletons
------------------------------------------------------------------------------}
--
prop-elements-singleton
  : ∀ {k a} ⦃ _ : Ord k ⦄ (key : k) (x : a)
  → elements (singleton key x) ≡ Bag.singleton x
--
prop-elements-singleton key x
  rewrite Map.prop-toAscList-singleton key (Bag.singleton x)
  = Monoid.rightIdentity _

--
@0 prop-merge-singleton
  : ∀ {k} ⦃ _ : Ord k ⦄ ⦃ _ : IsLawfulEq k ⦄
    (keyx : k) (x : a) (keyy : k) (y : b)
  → merge (singleton keyx x) (singleton keyy y)
    ≡ (if keyx == keyy then singleton keyx (x , y) else mempty)
--
prop-merge-singleton keyx x keyy y =
  prop-Table-equality
    (trans lemma (sym (prop-if-apply getTable (keyx == keyy) _ _)))
  where
    single : ∀ {c} {k} ⦃ _ : Ord k ⦄ → k → c → Map k (Bag c)
    single = λ key v → Map.singleton key (Bag.singleton v)

    lemma
      : mergeRaw (single keyx x) (single keyy y)
      ≡ (if keyx == keyy then single keyx (x , y) else Map.empty)
    lemma
      rewrite Map.prop-intersectionWith-singleton Bag.cartesianProduct keyx (Bag.singleton x) keyy (Bag.singleton y)
      with keyx == keyy
    ... | False = refl
    ... | True  = refl

{-----------------------------------------------------------------------------
    Properties
    Homomorphisms
------------------------------------------------------------------------------}
-- | 'lookup' is a homomorphism of monoids.
prop-morphism-lookup
  : ∀ {a k} ⦃ _ : Ord k ⦄
  → ∀ (key : k) → Monoid.IsHomomorphism (lookup {a} key)
--
prop-morphism-lookup {a} {k} key .Monoid.homo-mempty =
  cong toBag (Map.prop-lookup-empty key)
prop-morphism-lookup {a} {k} key .Monoid.homo-<> xs ys
  rewrite Map.prop-lookup-unionWith key (_<>_) (getTable xs) (getTable ys)
  with Map.lookup key (getTable xs) | Map.lookup key (getTable ys)
... | Nothing | Nothing = sym (Monoid.leftIdentity _)
... | Nothing | Just y  = sym (Monoid.leftIdentity _)
... | Just x  | Nothing = sym (Monoid.rightIdentity _)
... | Just x  | Just y  = refl

-- | 'indexBy' is a homomorphism of monoids.
prop-morphism-indexBy
  : ∀ {a k} ⦃ _ : Ord k ⦄
  → ∀ (f : a → k) → Monoid.IsHomomorphism (λ xs → indexBy xs f)
--
prop-morphism-indexBy f = Bag.prop-morphism-foldBag _

-- | 'elements' on 'Table' is a homomorphism of monoids.
@0 prop-morphism-elements
  : ∀ {a k} ⦃ _ : Ord k ⦄
  → Monoid.IsHomomorphism (elements {a} {k})
--
prop-morphism-elements {a} {k} .Monoid.homo-mempty
  rewrite Map.prop-toAscList-empty {k} {Bag a}
  = refl
prop-morphism-elements .Monoid.homo-<> x y =
  Map.prop-fold-unionWith (getTable x) (getTable y)

-- | 'merge' is a homomorphism of monoids in its first argument.
@0 prop-morphism-merge-1
  : ∀ {k} ⦃ _ : Ord k ⦄
  → ∀ (ys : Table k b) → Monoid.IsHomomorphism (λ xs → merge {a} xs ys)
--
prop-morphism-merge-1 zs .Monoid.homo-mempty =
  prop-Table-equality (Map.prop-intersectionWith-empty-x _ _)
prop-morphism-merge-1 zs .Monoid.homo-<> xs ys =
  prop-Table-equality
    (Map.prop-intersectionWith-unionWith-x _ _ _ _ _ _
      (λ x y z → (Bag.prop-morphism-cartesianProduct-1 z .Monoid.homo-<>) x y)
    )

-- | 'merge' is a homomorphism of monoids in its second argument.
@0 prop-morphism-merge-2
  : ∀ {k} ⦃ _ : Ord k ⦄
  → ∀ (xs : Table k a) → Monoid.IsHomomorphism (λ ys → merge {a} {b} xs ys)
--
prop-morphism-merge-2 xs .Monoid.homo-mempty =
  prop-Table-equality (Map.prop-intersectionWith-x-empty _ _)
prop-morphism-merge-2 xs .Monoid.homo-<> ys zs =
  prop-Table-equality
    (Map.prop-intersectionWith-x-unionWith _ _ _ _ _ _
      (λ x → Bag.prop-morphism-cartesianProduct-2 x .Monoid.homo-<>)
    )

-- | 'elements' is an inverse of 'indexBy'.
@0 prop-elements-indexBy
  : ∀ {k} ⦃ _ : Ord k ⦄ (xs : Bag a) (f : a → k)
  → elements (indexBy xs f) ≡ xs
--
prop-elements-indexBy {a} {k} xs f =
    Bag.prop-Bag-equality lhs rhs lhs-homo rhs-homo eq-singleton xs
  where
    lhs = λ xs → elements (indexBy xs f)
    rhs = λ xs → xs

    lhs-homo : Monoid.IsHomomorphism lhs
    lhs-homo =
      Monoid.prop-morphism-∘ _ _
        (prop-morphism-indexBy _) prop-morphism-elements

    rhs-homo = Monoid.prop-morphism-id

    eq-singleton : ∀ x → lhs (Bag.singleton x) ≡ rhs (Bag.singleton x)
    eq-singleton x = prop-elements-singleton (f x) x

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- | 'indexBy' filters items by 'key'.
prop-lookup-indexBy
  : ∀ {k} ⦃ _ : Ord k ⦄ (key : k) (xs : Bag a) (f : a → k)
  → lookup key (indexBy xs f)
    ≡ Bag.filter (λ x → key == f x) xs
--
prop-lookup-indexBy key xs f =
    Bag.prop-Bag-equality lhs rhs lhs-homo rhs-homo eq-singleton xs
  where
    lhs = λ xs → lookup key (indexBy xs f)
    rhs = λ xs → Bag.filter (λ x → key == f x) xs

    lhs-homo : Monoid.IsHomomorphism lhs
    lhs-homo =
      Monoid.prop-morphism-∘ _ _
        (prop-morphism-indexBy _) (prop-morphism-lookup key) 

    rhs-homo = Bag.prop-morphism-filter (λ x → key == f x)

    eq-singleton : ∀ x → lhs (Bag.singleton x) ≡ rhs (Bag.singleton x)
    eq-singleton x
      rewrite Map.prop-lookup-singleton key (f x) (Bag.singleton x)
      with key == f x
    ... | False = refl
    ... | True  = refl

-- | Using 'indexBy' for each key will give an efficient implementation
-- implementation of 'equijoin'.
--
-- Proof: We use a proof idea that differs from the one in the paper.
-- Specifically, we use uniqueness of morphism again!
-- The property holds because:
--   * When considered as maps from @xs@ or @ys@, the left-hand side
--     and the right-hand side are monoid homomorphisms, and
--   * it holds on 'Bag.singleton'.
@0 prop-equijoin-indexBy
  : ∀ {k} ⦃ _ : Ord k ⦄ ⦃ _ : IsLawfulEq k ⦄
      (f : a → k) (g : b → k) (xs : Bag a) (ys : Bag b)
  → Bag.equijoin f g xs ys
    ≡ elements (merge (indexBy xs f) (indexBy ys g))
--
prop-equijoin-indexBy {a} {b} {k} f g xs ys =
    Bag.prop-Bag-equality-2 lhs rhs
      (λ xs → Bag.prop-morphism-equijoin-2 f g xs)
      (λ xs → Monoid.prop-morphism-∘ _ _
        (Monoid.prop-morphism-∘ _ _
          (prop-morphism-indexBy g)
          (prop-morphism-merge-2 (indexBy xs f))
        )
        prop-morphism-elements)
      (λ ys → Bag.prop-morphism-equijoin-1 f g ys)
      (λ ys → Monoid.prop-morphism-∘ _ _
        (Monoid.prop-morphism-∘ _ _
          (prop-morphism-indexBy f)
          (prop-morphism-merge-1 (indexBy ys g))
        )
        prop-morphism-elements)
      eq-singleton xs ys
  where
    lhs = λ xs ys → Bag.equijoin f g xs ys
    rhs = λ xs ys → elements (merge (indexBy xs f) (indexBy ys g))

    eq-singleton
      : ∀ x y
      → lhs (Bag.singleton x) (Bag.singleton y)
        ≡ rhs (Bag.singleton x) (Bag.singleton y)
    eq-singleton x y
      with f x == g y in eq
    ... | False =
        begin
          mempty
        ≡⟨ sym (Monoid.homo-mempty prop-morphism-elements) ⟩
          elements (mempty {Table k (a × b)})
        ≡⟨ cong (λ o → elements (if o then singleton _ _ else mempty)) (sym eq) ⟩
          elements (if f x == g y then singleton (f x) (x , y) else mempty)
        ≡⟨ sym (cong elements (prop-merge-singleton (f x) x (g y) y)) ⟩
          elements (merge (singleton (f x) x) (singleton (g y) y)) 
        ∎
    ... | True  =
        begin
          Bag.singleton (x , y)
        ≡⟨ sym (prop-elements-singleton (f x) (x , y)) ⟩
          elements (singleton (f x) (x , y))
        ≡⟨ cong (λ o → elements (if o then singleton _ _ else mempty)) (sym eq) ⟩
          elements (if f x == g y then singleton (f x) (x , y) else mempty)
        ≡⟨ sym (cong elements (prop-merge-singleton (f x) x (g y) y)) ⟩
          elements (merge (singleton (f x) x) (singleton (g y) y)) 
        ∎
