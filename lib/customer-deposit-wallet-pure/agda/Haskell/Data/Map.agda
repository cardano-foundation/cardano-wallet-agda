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
    Helper predicates
------------------------------------------------------------------------------}
AntitonicPred : {a : Set} → {{Ord a}} → (a → Bool) → Set
AntitonicPred {a} p =
  ∀ {x y : a} → ((x <= y) ≡ True) → ((p x >= p y) ≡ True)

{-----------------------------------------------------------------------------
    Data.Maybe
------------------------------------------------------------------------------}

unionWithMaybe : (a → a → a) → Maybe a → Maybe a → Maybe a
unionWithMaybe f Nothing my = my
unionWithMaybe f (Just x) Nothing = Just x
unionWithMaybe f (Just x) (Just y) = Just (f x y)

intersectionWithMaybe : (a → b → c) → Maybe a → Maybe b → Maybe c
intersectionWithMaybe f (Just x) (Just y) = Just (f x y)
intersectionWithMaybe _ _ _ = Nothing

updateMaybe : (a → Maybe a) → Maybe a → Maybe a
updateMaybe f Nothing = Nothing
updateMaybe f (Just x) = f x

{-----------------------------------------------------------------------------
    Data.Map
------------------------------------------------------------------------------}

postulate
  Map : ∀ (k : Set) {{iOrd : Ord k}} → Set → Set

module _ {k a : Set} {{_ : Ord k}} where
  postulate
    lookup    : k → Map k a → Maybe a
    null      : Map k a → Bool
    toAscList : Map k a → List (k × a)

    empty     : Map k a
    insert    : k → a → Map k a → Map k a
    delete    : k → Map k a → Map k a
    update    : (a → Maybe a) → k → Map k a → Map k a
    fromList  : List (k × a) → Map k a
    fromListWith : (a → a → a) → List (k × a) → Map k a

    unionWith     : (a → a → a) → Map k a → Map k a → Map k a
    filterWithKey : (k → a → Bool) → Map k a → Map k a

    takeWhileAntitone : (k → Bool) → Map k a → Map k a
    dropWhileAntitone : (k → Bool) → Map k a → Map k a

    instance
      iMapFunctor : Functor (Map k)

    mapWithKey : (k → a → b) → Map k a → Map k b

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

    prop-lookup-update
      : ∀ (key keyi : k) (m : Map k a) (f : a → Maybe a)
      → lookup key (update f keyi m)
        ≡ (if (key == keyi) then (lookup keyi m >>= f) else lookup key m)


    prop-lookup-toAscList-Just
      : ∀ (key : k) (x : a) (m : Map k a)
      → lookup key m ≡ Just x
      → (elem key ∘ L.map fst ∘ toAscList) m ≡ True

    prop-lookup-toAscList-Nothing
      : ∀ (key : k) (m : Map k a)
      → lookup key m ≡ Nothing
      → (elem key ∘ L.map fst ∘ toAscList) m ≡ False

    prop-lookup-unionWith
      : ∀ (key : k) (m n : Map k a) (f : a → a → a)
      → lookup key (unionWith f m n)
        ≡ unionWithMaybe f (lookup key m) (lookup key n)

    prop-lookup-filterWithKey-Just
      : ∀ (key : k) (x : a) (m : Map k a) (p : k → a → Bool)
      → lookup key m ≡ Just x
      → lookup key (filterWithKey p m)
        ≡ (if p key x then Just x else Nothing)
    
    prop-lookup-filterWithKey-Nothing
      : ∀ (key : k) (m : Map k a) (p : k → a → Bool)
      → lookup key m ≡ Nothing
      → lookup key (filterWithKey p m) ≡ Nothing

    prop-lookup-takeWhileAntitone
      : ∀ (p : k → Bool) → AntitonicPred p
      → ∀ (key : k) (m : Map k a)
      → lookup key (takeWhileAntitone p m)
        ≡ lookup key (filterWithKey (λ k _ → p k) m)

    prop-lookup-dropWhileAntitone
      : ∀ (p : k → Bool) → AntitonicPred p
      → ∀ (key : k) (m : Map k a)
      → lookup key (dropWhileAntitone p m)
        ≡ lookup key (filterWithKey (λ k _ → not (p k)) m)

  map : ∀ {b : Set} → (a → b) → Map k a → Map k b
  map = fmap

  member : k → Map k a → Bool
  member key = isJust ∘ lookup key

  elems : Map k a → List a
  elems = List.map snd ∘ toAscList

  keys : Map k a → List k
  keys = List.map fst ∘ toAscList

  keysSet : Map k a → Set.ℙ k
  keysSet = Set.fromList ∘ keys

  singleton : k → a → Map k a
  singleton = λ k x → insert k x empty

  alter : (Maybe a → Maybe a) → k → Map k a → Map k a
  alter f k m = case f (lookup k m) of λ where
    Nothing → delete k m
    (Just a) → insert k a m

  insertWith : (a → a → a) → k → a → Map k a → Map k a
  insertWith f k new m = case lookup k m of λ where
    Nothing → insert k new m
    (Just old) → insert k (f new old) m

  withoutKeys : Map k a → Set.ℙ k → Map k a
  withoutKeys m s = filterWithKey (λ k _ → not (Set.member k s)) m

  restrictKeys : Map k a → Set.ℙ k → Map k a
  restrictKeys m s = filterWithKey (λ k _ → Set.member k s) m

  filter : (a → Bool) → Map k a → Map k a
  filter p = filterWithKey (λ _ x → p x)

  spanAntitone : (k → Bool) → Map k a → (Map k a × Map k a)
  spanAntitone p m = (takeWhileAntitone p m , dropWhileAntitone p m)

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

postulate
  prop-lookup-fmap
    : ∀ {a b k : Set} {{_ : Ord k}}
        (key : k)
        (m : Map k a)
        (f : a → b)
    → lookup key (fmap {{iMapFunctor {k} {a}}} f m)
      ≡ fmap f (lookup key m)

  prop-lookup-mapWithKey
    : ∀ {a b k : Set} {{_ : Ord k}}
        (key : k)
        (m : Map k a)
        (f : k → a → b)
    → lookup key (mapWithKey f m)
      ≡ fmap (f key) (lookup key m)

instance
  iMapFoldable : ∀ {k : Set} {{_ : Ord k}} → Foldable (Map k)
  iMapFoldable =
    record {DefaultFoldable (record {foldMap = foldMap'})}

module _ {k a b c : Set} {{_ : Ord k}} where
  postulate
    intersectionWith : (a → b → c) → Map k a → Map k b → Map k c

    prop-lookup-intersectionWith
      : ∀ (key : k) (ma : Map k a) (mb : Map k b)
          (f : a → b → c)
      → lookup key (intersectionWith f ma mb)
        ≡ intersectionWithMaybe f (lookup key ma) (lookup key mb)

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
