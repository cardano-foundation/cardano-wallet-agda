{-# OPTIONS --erasure #-}

module Haskell.Data.Map
    {-
    ; Map
      ; lookup
      ; null
      ; insert
    -}
    where

open import Haskell.Prelude hiding (lookup; null; map; filter)
import Haskell.Prelude as L using (map)

open import Haskell.Data.Maybe using
    ( isJust
    )

import Haskell.Prelude as List using (map)
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    Helpers
------------------------------------------------------------------------------}

-- These lemmas are obvious substitutions,
-- but substitution in a subterm is sometimes cumbersome
-- with equational reasoning.
lemma-if-True
  : ∀ {A B : Set} {{_ : Eq A}} (x x' : A) {t f : B}
  → (x == x') ≡ True
  → (if (x == x') then t else f) ≡ t
lemma-if-True _ _ eq1 rewrite eq1 = refl

lemma-if-False
  : ∀ {A B : Set} {{_ : Eq A}} (x x' : A) {t f : B}
  → (x == x') ≡ False
  → (if (x == x') then t else f) ≡ f
lemma-if-False _ _ eq1 rewrite eq1 = refl

{-----------------------------------------------------------------------------
    Data.Map
------------------------------------------------------------------------------}

postulate
  Map : ∀ (k : Set) {{iOrd : Ord k}} → Set → Set

module
    OperationsAndProperties
      {k a : Set}
      {{_ : Ord k}}
  where
  postulate
    lookup    : k → Map k a → Maybe a
    null      : Map k a → Bool
    toAscList : Map k a → List (k × a)

    empty     : Map k a
    insert    : k → a → Map k a → Map k a
    delete    : k → Map k a → Map k a
    fromList  : List (k × a) → Map k a
    fromListWith : (a → a → a) → List (k × a) → Map k a

    unionWith     : (a → a → a) → Map k a → Map k a → Map k a
    filterWithKey : (k → a → Bool) → Map k a → Map k a

    instance
      iMapFunctor : Functor (Map k)

    prop-member-null
      : ∀ (m : Map k a)
          (_ : ∀ (key : k) → lookup key m ≡ Nothing)
      → null m ≡ True

    prop-null-empty
      : ∀ (m : Map k a)
      → null m ≡ True
      → m ≡ empty

    prop-lookup-empty
      : ∀ (key : k)
      → lookup key empty ≡ Nothing

    prop-lookup-insert
      : ∀ (key keyi : k) (x : a) (m : Map k a)
      → lookup key (insert keyi x m)
        ≡ (if (key == keyi) then Just x else lookup key m)

    prop-lookup-delete
      : ∀ (key keyi : k) (m : Map k a)
      → lookup key (delete keyi m)
        ≡ (if (key == keyi) then Nothing else lookup key m)

    prop-lookup-toAscList-Just
      : ∀ (key : k) (x : a) (m : Map k a)
      → lookup key m ≡ Just x
      → (elem key ∘ L.map fst ∘ toAscList) m ≡ True

    prop-lookup-toAscList-Nothing
      : ∀ (key : k) (m : Map k a)
      → lookup key m ≡ Nothing
      → (elem key ∘ L.map fst ∘ toAscList) m ≡ False

    prop-lookup-filterWithKey-Just
      : ∀ (key : k) (x : a) (m : Map k a) (p : k → a → Bool)
      → lookup key m ≡ Just x
      → lookup key (filterWithKey p m)
        ≡ (if p key x then Just x else Nothing)
    
    prop-lookup-filterWithKey-Nothing
      : ∀ (key : k) (m : Map k a) (p : k → a → Bool)
      → lookup key m ≡ Nothing
      → lookup key (filterWithKey p m) ≡ Nothing

  map : ∀ {b : Set} → (a → b) → Map k a → Map k b
  map = fmap

  member : k → Map k a → Bool
  member key = isJust ∘ lookup key

  keysSet : Map k a → Set.ℙ k
  keysSet = Set.fromList ∘ List.map fst ∘ toAscList

  singleton : k → a → Map k a
  singleton = λ k x → insert k x empty

  withoutKeys : Map k a → Set.ℙ k → Map k a
  withoutKeys m s = filterWithKey (λ k _ → not (Set.member k s)) m

  filter : (a → Bool) → Map k a → Map k a
  filter p = filterWithKey (λ _ x → p x)

  prop-lookup-singleton
    : ∀ (key keyi : k) (x : a)
    → lookup key (singleton keyi x)
      ≡ (if (key == keyi) then Just x else Nothing)
  prop-lookup-singleton key keyi x =
    begin
      lookup key (singleton keyi x)
    ≡⟨⟩
      lookup key (insert keyi x empty)
    ≡⟨ prop-lookup-insert key keyi x empty ⟩
      (if (key == keyi) then Just x else lookup key empty)
    ≡⟨ cong (λ f → if (key == keyi) then Just x else f) (prop-lookup-empty key) ⟩
      (if (key == keyi) then Just x else Nothing)
    ∎

  foldMap' : ∀ {{_ : Monoid b}} → (a → b) → Map k a → b
  foldMap' f = foldMap f ∘ L.map snd ∘ toAscList

open OperationsAndProperties public

instance
  iMapFoldable : ∀ {k : Set} {{_ : Ord k}} → Foldable (Map k)
  iMapFoldable =
    record {DefaultFoldable (record {foldMap = foldMap'})}

{-----------------------------------------------------------------------------
    Test proofs
------------------------------------------------------------------------------}

filterMaybe
  : ∀ {a : Set} → (a → Bool) → Maybe a → Maybe a
filterMaybe p Nothing = Nothing
filterMaybe p (Just x) = if p x then Just x else Nothing

@0 prop-lookup-filter
  : ∀ {k a} {{_ : Ord k}}
      (key : k) (p : a → Bool) (m : Map k a) 
  → lookup key (filter p m)
    ≡ filterMaybe p (lookup key m)
prop-lookup-filter key p m = case lookup key m of λ where
  (Just x) {{eq}} →
    begin
      lookup key (filter p m)
    ≡⟨ prop-lookup-filterWithKey-Just key x m (λ _ x → p x) eq ⟩
      (if p x then Just x else Nothing)
    ≡⟨⟩
      filterMaybe p (Just x)
    ≡⟨ cong (filterMaybe p) (sym eq) ⟩
      filterMaybe p (lookup key m)
    ∎
  Nothing {{eq}} →
    begin
      lookup key (filter p m)
    ≡⟨ prop-lookup-filterWithKey-Nothing key m (λ _ x → p x) eq ⟩
      Nothing
    ≡⟨⟩
      filterMaybe p Nothing
    ≡⟨ cong (filterMaybe p) (sym eq) ⟩
      filterMaybe p (lookup key m)
    ∎

--
@0 prop-withoutKeys-empty
  : ∀ {k a} {{_ : Ord k}}
      (key : k) (m : Map k a)
  → lookup key (withoutKeys m Set.empty)
    ≡ lookup key m
--
prop-withoutKeys-empty {k} {a} key m =
  case (lookup key m) of λ where
    (Just x) {{eq}} →
      begin
        lookup key (withoutKeys m Set.empty)
      ≡⟨ prop-lookup-filterWithKey-Just key x m p eq ⟩
        (if p key x then Just x else Nothing)
      ≡⟨ cong (λ b → if not b then Just x else Nothing) (Set.prop-member-empty key) ⟩
        (if True then Just x else Nothing)
      ≡⟨ sym eq ⟩
        lookup key m
      ∎
    Nothing {{eq}} →
      begin
        lookup key (withoutKeys m Set.empty)
      ≡⟨ prop-lookup-filterWithKey-Nothing key m p eq ⟩
        Nothing
      ≡⟨ sym eq ⟩
        lookup key m
      ∎
  where
    p : k → a → Bool
    p = λ k _ → not (Set.member k Set.empty)
