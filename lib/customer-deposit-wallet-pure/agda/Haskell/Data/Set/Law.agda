{-# OPTIONS --erasure #-}

-- | Proofs on 'Set'.
module Haskell.Data.Set.Law where

open import Haskell.Reasoning
open import Haskell.Prelude hiding (lookup; null; map; filter)

open import Haskell.Data.Set.Def

{-# FOREIGN AGDA2HS
type DummyDataSetLaw = ()
#-}

{-----------------------------------------------------------------------------
    Proofs
    involving 1 value type
------------------------------------------------------------------------------}

module _ {a : Set} {{_ : Ord a}} where

  --
  prop-null-empty
    : null {a} empty ≡ True
  --
  prop-null-empty =
    prop-member-null empty prop-member-empty 

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
 
  -- |
  -- The 'empty' set is a subset of every set.
  prop-isSubsetOf-empty
    : ∀ {s : ℙ a}
    → isSubsetOf empty s ≡ True
  --
  prop-isSubsetOf-empty {s} =
    prop-intersection→isSubsetOf empty s prop-intersection-empty-left
