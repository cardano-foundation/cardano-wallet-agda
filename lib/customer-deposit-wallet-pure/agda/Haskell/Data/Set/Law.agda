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
    Properties
    Basic
------------------------------------------------------------------------------}
module _ {a : Set} {{_ : Ord a}} where

  --
  prop-null-empty
    : null {a} empty ≡ True
  --
  prop-null-empty =
    prop-member-null empty prop-member-empty 

{-----------------------------------------------------------------------------
    Properties
    https://en.wikipedia.org/wiki/Boolean_algebra_(structure)
------------------------------------------------------------------------------}
module _ {a : Set} {{_ : Ord a}} where

  --
  prop-union-idem
    : ∀ {sa : ℙ a}
    → union sa sa
        ≡ sa
  --
  prop-union-idem {sa} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (union sa sa) ≡ member x sa
      eq x
        rewrite prop-member-union x sa sa
        rewrite prop-||-idem (member x sa)
        = refl

  --
  prop-union-assoc
    : ∀ {sa sb sc : ℙ a}
    → union (union sa sb) sc
      ≡ union sa (union sb sc)
  --
  prop-union-assoc {sa} {sb} {sc} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (union (union sa sb) sc)
          ≡ member x (union sa (union sb sc))
      eq x
        rewrite prop-member-union x (union sa sb) sc
        rewrite prop-member-union x sa sb
        rewrite prop-member-union x sa (union sb sc)
        rewrite prop-member-union x sb sc
        rewrite prop-||-assoc (member x sa) (member x sb) (member x sc)
        = refl

  --
  prop-union-sym
    : ∀ {sa sb : ℙ a}
    → union sa sb
        ≡ union sb sa
  --
  prop-union-sym {sa} {sb} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (union sa sb) ≡ member x (union sb sa)
      eq x
        rewrite prop-member-union x sa sb
        rewrite prop-member-union x sb sa
        rewrite prop-||-sym (member x sa) (member x sb)
        = refl

  --
  prop-union-absorb
    : ∀ {sa sb : ℙ a}
    → union sa (intersection sa sb)
      ≡ sa
  --
  prop-union-absorb {sa} {sb} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (union sa (intersection sa sb)) ≡ member x sa
      eq x
        rewrite prop-member-union x sa (intersection sa sb)
        rewrite prop-member-intersection x sa sb
        rewrite prop-||-absorb (member x sa) (member x sb)
        = refl

  --
  prop-union-identity
    : ∀ {sa : ℙ a}
    → union sa empty
      ≡ sa
  --
  prop-union-identity {sa} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (union sa empty) ≡ member x sa
      eq x
        rewrite prop-member-union x sa empty
        rewrite prop-member-empty x
        rewrite prop-||-identity (member x sa)
        = refl

  --
  prop-union-intersection-distribute
    : ∀ {sa sb sc : ℙ a}
    → union sa (intersection sb sc)
      ≡ intersection (union sa sb) (union sa sc)
  --
  prop-union-intersection-distribute {sa} {sb} {sc} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (union sa (intersection sb sc))
          ≡ member x (intersection (union sa sb) (union sa sc))
      eq x
        rewrite prop-member-union x sa (intersection sb sc)
        rewrite prop-member-intersection x sb sc
        rewrite prop-member-intersection x (union sa sb) (union sa sc)
        rewrite prop-member-union x sa sb
        rewrite prop-member-union x sa sc
        rewrite prop-||-&&-distribute (member x sa) (member x sb) (member x sc)
        = refl


  --
  prop-intersection-idem
    : ∀ {sa : ℙ a}
    → intersection sa sa
        ≡ sa
  --
  prop-intersection-idem {sa} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection sa sa) ≡ member x sa
      eq x
        rewrite prop-member-intersection x sa sa
        rewrite prop-&&-idem (member x sa)
        = refl

  --
  prop-intersection-assoc
    : ∀ {sa sb sc : ℙ a}
    → intersection (intersection sa sb) sc
      ≡ intersection sa (intersection sb sc)
  --
  prop-intersection-assoc {sa} {sb} {sc} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection (intersection sa sb) sc)
          ≡ member x (intersection sa (intersection sb sc))
      eq x
        rewrite prop-member-intersection x (intersection sa sb) sc
        rewrite prop-member-intersection x sa sb
        rewrite prop-member-intersection x sa (intersection sb sc)
        rewrite prop-member-intersection x sb sc
        rewrite prop-&&-assoc (member x sa) (member x sb) (member x sc)
        = refl

  --
  prop-intersection-sym
    : ∀ {sa sb : ℙ a}
    → intersection sa sb
        ≡ intersection sb sa
  --
  prop-intersection-sym {sa} {sb} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection sa sb) ≡ member x (intersection sb sa)
      eq x
        rewrite prop-member-intersection x sa sb
        rewrite prop-member-intersection x sb sa
        rewrite prop-&&-sym (member x sa) (member x sb)
        = refl

  --
  prop-intersection-absorb
    : ∀ {sa sb : ℙ a}
    → intersection sa (union sa sb)
      ≡ sa
  --
  prop-intersection-absorb {sa} {sb} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection sa (union sa sb)) ≡ member x sa
      eq x
        rewrite prop-member-intersection x sa (union sa sb)
        rewrite prop-member-union x sa sb
        rewrite prop-&&-absorb (member x sa) (member x sb)
        = refl

  --
  prop-intersection-union-distribute
    : ∀ {sa sb sc : ℙ a}
    → intersection sa (union sb sc)
      ≡ union (intersection sa sb) (intersection sa sc)
  --
  prop-intersection-union-distribute {sa} {sb} {sc} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection sa (union sb sc))
          ≡ member x (union (intersection sa sb) (intersection sa sc))
      eq x
        rewrite prop-member-intersection x sa (union sb sc)
        rewrite prop-member-union x sb sc
        rewrite prop-member-union x (intersection sa sb) (intersection sa sc)
        rewrite prop-member-intersection x sa sb
        rewrite prop-member-intersection x sa sc
        rewrite prop-&&-||-distribute (member x sa) (member x sb) (member x sc)
        = refl

  --
  prop-intersection-empty-right
    : ∀ {sa : ℙ a}
    → intersection sa empty
      ≡ empty
  --
  prop-intersection-empty-right {sa} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection sa empty) ≡ member x empty
      eq x
        rewrite prop-member-intersection x sa empty
        rewrite prop-member-empty x
        rewrite prop-x-&&-False (member x sa)
        = refl

  --
  prop-intersection-empty-left
    : ∀ {sa : ℙ a}
    → intersection empty sa
      ≡ empty
  --
  prop-intersection-empty-left {sa} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection empty sa) ≡ member x empty
      eq x
        rewrite prop-member-intersection x empty sa
        rewrite prop-member-empty x
        = refl

{-----------------------------------------------------------------------------
    Properties
    involving  difference
------------------------------------------------------------------------------}
module _ {a : Set} {{_ : Ord a}} where

  --
  prop-intersection-difference
    : ∀ {sa sb : ℙ a}
    → intersection sb (difference sa sb)
      ≡ empty
  --
  prop-intersection-difference {sa} {sb} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (intersection sb (difference sa sb)) ≡ member x empty
      eq x
        rewrite prop-member-intersection x sb (difference sa sb)
        rewrite prop-member-difference x sa sb
        rewrite prop-member-empty x
        with member x sa
        with member x sb
      ... | True  | True  = refl
      ... | False | True  = refl
      ... | True  | False = refl
      ... | False | False = refl

  --
  prop-disjoint-difference
    : ∀ {sa sb : ℙ a}
    → disjoint sb (difference sa sb)
      ≡ True
  --
  prop-disjoint-difference {sa} {sb} =
    trans (cong null prop-intersection-difference) prop-null-empty

  --
  prop-deMorgan-difference-intersection
    : ∀ {sa sb sc : ℙ a}
    → difference sa (intersection sb sc)
      ≡ union (difference sa sb) (difference sa sc)
  --
  prop-deMorgan-difference-intersection {sa} {sb} {sc} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (difference sa (intersection sb sc))
          ≡ member x (union (difference sa sb) (difference sa sc))
      eq x
        rewrite prop-member-difference x sa (intersection sb sc)
        rewrite prop-member-intersection x sb sc
        rewrite prop-member-union x (difference sa sb) (difference sa sc)
        rewrite prop-member-difference x sa sb
        rewrite prop-member-difference x sa sc
        with member x sa
      ... | False = refl
      ... | True  = prop-deMorgan-not-&& (member x sb) (member x sc)

  --
  prop-deMorgan-difference-union
    : ∀ {sa sb sc : ℙ a}
    → difference sa (union sb sc)
      ≡ intersection (difference sa sb) (difference sa sc)
  --
  prop-deMorgan-difference-union {sa} {sb} {sc} = prop-equality eq
    where
      eq
        : ∀ (x : a)
        → member x (difference sa (union sb sc))
          ≡ member x (intersection (difference sa sb) (difference sa sc))
      eq x
        rewrite prop-member-difference x sa (union sb sc)
        rewrite prop-member-union x sb sc
        rewrite prop-member-intersection x (difference sa sb) (difference sa sc)
        rewrite prop-member-difference x sa sb
        rewrite prop-member-difference x sa sc
        with member x sa
      ... | False = refl
      ... | True  = prop-deMorgan-not-|| (member x sb) (member x sc)

{-----------------------------------------------------------------------------
    Properties
    involving  isSubsetOf
------------------------------------------------------------------------------}
module _ {a : Set} {{_ : Ord a}} where

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
        rewrite lem1 (member x s1) (member x s2)
        = refl
 
  -- |
  -- The 'empty' set is a subset of every set.
  prop-isSubsetOf-empty
    : ∀ {s : ℙ a}
    → isSubsetOf empty s ≡ True
  --
  prop-isSubsetOf-empty {s} =
    prop-intersection→isSubsetOf empty s prop-intersection-empty-left
