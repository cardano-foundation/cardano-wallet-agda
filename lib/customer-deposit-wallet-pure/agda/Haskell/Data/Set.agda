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

    map        : ∀ {b} {{_ : Ord b}} → (a → b) → ℙ a → ℙ b
    union      : ℙ a → ℙ a → ℙ a
    difference : ℙ a → ℙ a → ℙ a
    filter     : (a → Bool) → ℙ a → ℙ a

    prop-member-null
      : ∀ (s : ℙ a)
          (_ : ∀ (x : a) → member x s ≡ False)
      → null s ≡ True

    prop-null-empty
      : ∀ (s : ℙ a)
      → null s ≡ True
      → s ≡ empty

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

    prop-member-union
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (union s1 s2)
        ≡ (member x s1 || member x s2)

    prop-member-difference    
      : ∀ (x : a) (s1 s2 : ℙ a)
      → member x (difference s1 s2)
        ≡ (member x s1 && not (member x s2))
    
    prop-member-filter    
      : ∀ (x : a) (p : a → Bool) (s : ℙ a)
      → member x (filter p s)
        ≡ (p x && member x s)

  singleton : a → ℙ a
  singleton = λ x → insert x empty

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
