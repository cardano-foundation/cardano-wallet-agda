{-# OPTIONS --erasure #-}

module Haskell.Data.Set
    {-
    ; ℙ
      ; member
      ; null
      ; toAscList
      ; empty
      ; insert
      ; delete
      ; fromList
      ; map
      ; union 
    -}
    where

open import Haskell.Prelude hiding (null; map; filter)
open import Haskell.Reasoning

import Haskell.Prelude as L using (map)

{-----------------------------------------------------------------------------
    Data.Set
------------------------------------------------------------------------------}

-- | As the term 'Set' is already taken in Agda, we use ℙ (\bP).
postulate
  ℙ : Set → Set

module _ {a : Set} where
  postulate
    toAscList : ℙ a → List a
    null      : ℙ a → Bool

module _ {a : Set} {{_ : Ord a}} where
  postulate
    member    : a → ℙ a → Bool

    empty     : ℙ a
    insert    : a → ℙ a → ℙ a
    delete    : a → ℙ a → ℙ a
    fromList  : List a → ℙ a

    map          : ∀ {b} {{_ : Ord b}} → (a → b) → ℙ a → ℙ b
    union        : ℙ a → ℙ a → ℙ a
    intersection : ℙ a → ℙ a → ℙ a
    difference   : ℙ a → ℙ a → ℙ a
    filter       : (a → Bool) → ℙ a → ℙ a

    isSubsetOf   : ℙ a → ℙ a → Bool

    prop-member-null
      : ∀ (s : ℙ a)
          (_ : ∀ (x : a) → member x s ≡ False)
      → null s ≡ True

    prop-null→empty
      : ∀ (s : ℙ a)
      → null s ≡ True
      → s ≡ empty

    prop-equality
      : ∀ {s1 s2 : ℙ a}
      → (∀ (x : a) → member x s1 ≡ member x s2)
      → s1 ≡ s2

    prop-member-empty
      : ∀ (x : a)
      → member x empty ≡ False

    prop-member-insert
      : ∀ (x xi : a) (s : ℙ a)
      → member x (insert xi s)
        ≡ (if (x == xi) then True else member x s)

    prop-member-delete
      : ∀ (x xi : a) (s : ℙ a)
      → member x (delete xi s)
        ≡ (if (x == xi) then False else member x s)

    prop-member-toAscList
      : ∀ (x : a) (s : ℙ a)
      → (elem x ∘ toAscList) s ≡ member x s

    prop-member-fromList
      : ∀ (x : a) (xs : List a)
      → member x (fromList xs)
        ≡ elem x xs

    prop-member-union
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (union s1 s2)
        ≡ (member x s1 || member x s2)

    prop-member-intersection    
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (intersection s1 s2)
        ≡ (member x s1 && member x s2)

    prop-member-difference    
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (difference s1 s2)
        ≡ (member x s1 && not (member x s2))
    
    prop-member-filter    
      : ∀ (x : a) (p : a → Bool) (s : ℙ a)
      → member x (filter p s)
        ≡ (p x && member x s)

    prop-isSubsetOf→intersection
      : ∀ (s1 s2 : ℙ a)
      → isSubsetOf s1 s2 ≡ True
      → intersection s1 s2 ≡ s1

    prop-intersection→isSubsetOf
      : ∀ (s1 s2 : ℙ a)
      → intersection s1 s2 ≡ s1
      → isSubsetOf s1 s2 ≡ True

  singleton : a → ℙ a
  singleton = λ x → insert x empty

  disjoint : ℙ a → ℙ a → Bool
  disjoint m = null ∘ intersection m

foldMap' : ∀ {{_ : Monoid b}} → (a → b) → ℙ a → b
foldMap' f = foldMap f ∘ toAscList

postulate
  prop-member-map
    : ∀ {a b} {{_ : Ord a}} {{_ : Ord b}}
      (x : a) (s : ℙ a) (f : a → b)
    → member (f x) (map f s) ≡ member x s

instance
  iSetFoldable : Foldable ℙ
  iSetFoldable =
    record {DefaultFoldable (record {foldMap = foldMap'})}

  iSetSemigroup : {{Ord a}} → Semigroup (ℙ a)
  iSetSemigroup ._<>_ = union

  iSetMonoid : {{Ord a}} → Monoid (ℙ a)
  iSetMonoid = record {DefaultMonoid (record {mempty = empty})}

module _ {a : Set} {{_ : Ord a}} where
  --
  prop-union-sym
    : ∀ {s1 s2 : ℙ a}
    → union s1 s2 ≡ union s2 s1
  --
  prop-union-sym {s1} {s2} =
      prop-equality eq
    where
      eq = λ x →
        begin
          member x (union s1 s2)
        ≡⟨ prop-member-union _ _ _ ⟩
          (member x s1 || member x s2)
        ≡⟨ prop-||-sym (member x s1) (member x s2) ⟩
          (member x s2 || member x s1)
        ≡⟨ sym (prop-member-union _ _ _) ⟩
          member x (union s2 s1)
        ∎

  --
  prop-union-assoc
    : ∀ {s1 s2 s3 : ℙ a}
    → union (union s1 s2) s3
      ≡ union s1 (union s2 s3)
  --
  prop-union-assoc {s1} {s2} {s3} =
      prop-equality eq
    where
      eq = λ x →
        begin
          member x (union (union s1 s2) s3)
        ≡⟨ prop-member-union _ _ _ ⟩
          (member x (union s1 s2) || member x s3)
        ≡⟨ cong (λ o → o || _) (prop-member-union _ _ _) ⟩
          ((member x s1 || member x s2) || member x s3)
        ≡⟨ prop-||-assoc (member x s1) (member x s2) (member x s3) ⟩
          (member x s1 || (member x s2 || member x s3))
        ≡⟨ sym (cong (λ o → _ || o) (prop-member-union _ _ _)) ⟩
          (member x s1 || member x (union s2 s3))
        ≡⟨ sym (prop-member-union _ _ _) ⟩
          member x (union s1 (union s2 s3))
        ∎

  --
  prop-intersection-empty-right
    : ∀ {s : ℙ a}
    → intersection s empty ≡ empty
  --
  prop-intersection-empty-right {s} = prop-equality eq
    where
      eq = λ x → begin
          member x (intersection s empty)
        ≡⟨ prop-member-intersection x s empty ⟩
          (member x s && member x empty)
        ≡⟨ cong (λ o → member x s && o) (prop-member-empty x) ⟩
          (member x s && False)
        ≡⟨ prop-x-&&-False (member x s) ⟩
          False
        ≡⟨ sym (prop-member-empty x) ⟩
          member x empty
        ∎

  --
  prop-intersection-empty-left
    : ∀ {s : ℙ a}
    → intersection empty s ≡ empty
  --
  prop-intersection-empty-left {s} = prop-equality eq
    where
      eq = λ x → begin
          member x (intersection empty s)
        ≡⟨ prop-member-intersection x empty s ⟩
          (member x empty && member x s)
        ≡⟨ cong (λ o → o && member x s) (prop-member-empty x) ⟩
          False
        ≡⟨ sym (prop-member-empty x) ⟩
          member x empty
        ∎

  --
  prop-intersection-isSubsetOf
    : ∀ {s1 s2 : ℙ a}
    → isSubsetOf (intersection s1 s2) s2 ≡ True
  --
  prop-intersection-isSubsetOf {s1} {s2} =
      prop-intersection→isSubsetOf _ _ (prop-equality lem2)
    where
      lem1
        : (x y : Bool)
        → ((x && y) && y) ≡ (x && y)
      lem1 x y
        rewrite prop-&&-assoc x y y
        rewrite prop-&&-idem y
        = refl

      lem2
        : ∀ (x : a)
        → member x (intersection (intersection s1 s2) s2)
            ≡ member x (intersection s1 s2)
      lem2 x
        rewrite prop-member-intersection x (intersection s1 s2) s2
        rewrite prop-member-intersection x s1 s2
        = lem1 (member x s1) (member x s2)
 