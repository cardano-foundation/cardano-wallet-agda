{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.RollbackWindow
  {-|
  -- * Definition
  ; RollbackWindow
    ; tip
    ; finality
    ; prop-RollbackWindow-invariant
  ; member
    ; prop-member-tip
    ; prop-member-finality
  ; singleton
    ; prop-member-singleton

  -- * Operations
  -- ** Rolling
  ; rollForward
  ; MaybeRollback (..)
  ; rollBackward
  ; prune

  -- ** Other
  ; intersection
  -} where

open import Haskell.Prelude hiding
    ( null
    )
open import Haskell.Reasoning

open import Haskell.Data.Maybe using
    ( isJust
    ; prop-Just-injective
    )
open import Haskell.Data.Set using
    ( ℙ
    )

import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    Helpers
------------------------------------------------------------------------------}
-- | (Internal function, exported for technical reasons.)
if'
  : (b : Bool)
  → (thn : @0 (b ≡ True) → a)
  → (els : @0 (b ≡ False) → a)
  → a
if' True thn els = thn refl
if' False thn els = els refl 

{-# COMPILE AGDA2HS if' #-}

prop-if'-False
  : ∀ {b : Bool}
  → (cond : b ≡ False)
  → {thn : @0 (b ≡ True) → a}
  → {els : @0 (b ≡ False) → a}
  → if' b thn els ≡ els cond
prop-if'-False {a} .{False} refl = refl

prop-if'-True
  : ∀ {b : Bool}
  → (cond : b ≡ True)
  → {thn : @0 (b ≡ True) → a}
  → {els : @0 (b ≡ False) → a}
  → if' b thn els ≡ thn cond
prop-if'-True {a} .{True} refl = refl

-- Substitution that also amends an equality proof.
substWithEq
  : ∀ {A B : Set} {x : A} (f : (a1 : A) → @0 (x ≡ a1) → B)
  → {y : A} → (eq : x ≡ y) → (f x refl ≡ f y eq)
substWithEq f refl = refl

{-----------------------------------------------------------------------------
    RollbackWindow
------------------------------------------------------------------------------}
-- | A 'RollbackWindow' is a time interval.
-- This time interval is used to keep track of data / transactions
-- that are not final and may still be rolled back.
-- 
-- * 'tip' is the higher end of the interval,
-- representing the latest state of the data.
-- * 'finality' is the lower end of the interval,
-- until which rollbacks are supported.
record RollbackWindow (time : Set) {{@0 _ : Ord time}} : Set where
  constructor RollbackWindowC
  field
    finality : time
    tip : time
    @0 invariant : (finality <= tip) ≡ True

open RollbackWindow public

-- |
-- Invariant: 'finality' is always before or equal to the 'tip'.
@0 prop-RollbackWindow-invariant
  : ∀ {time} {{_ : Ord time}}
      (w : RollbackWindow time)
  → (finality w <= tip w) ≡ True
--
prop-RollbackWindow-invariant = invariant

open RollbackWindow public

-- | Test whether a given time is within a 'RollbackWindow'.
member
    : ∀ {time} {{_ : Ord time}}
    → time → RollbackWindow time → Bool
member time w = (finality w <= time) && (time <= tip w)

-- | Interval containing a single point.
singleton
    : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
    → time → RollbackWindow time
singleton time = record
    { tip = time
    ; finality = time
    ; invariant = reflexivity time
    }

-- | Move forward the tip of the 'RollbackWindow'.
-- Return 'Nothing' if the new tip would not actually be moving forward.
rollForward
    : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
    → time → RollbackWindow time → Maybe (RollbackWindow time)
rollForward newTip w =
  if'
    (tip w < newTip)
    (λ cond → Just (record
      { finality = finality w
      ; tip = newTip
      ; invariant =
        transitivity
          (finality w) (tip w) newTip
          (prop-⋀-&& (invariant w `and` (lt2lte (tip w) newTip cond)))
      }))
    (λ cond → Nothing)

-- | Potential results of a 'rollBackwards'.
data MaybeRollback (a : Set) : Set where
    Past : MaybeRollback a
    Present : a → MaybeRollback a
    Future : MaybeRollback a

-- | Roll back the tip of the 'RollbackWindow' to a point within the window.
-- Return different error conditions if the target is outside the window.
rollBackward
    : ∀ {time} {{_ : Ord time}}
    → time → RollbackWindow time → MaybeRollback (RollbackWindow time)
rollBackward newTip w =
  if' (tip w <= newTip)
    (λ cond0 → Future)
    (λ cond0 →
      if' (finality w <= newTip)
        (λ cond → Present (record
          { tip = newTip
          ; finality = finality w
          ; invariant = cond
          }))
        (λ cond → Past)
    )

-- | Move forward the finality of the 'RollbackWindow'.
-- Return 'Nothing' if the finality is not moving forward, or too far.
prune
    : ∀ {time} {{_ : Ord time}}
    → time → RollbackWindow time → Maybe (RollbackWindow time)
prune newFinality w =
  if member newFinality w
    then (λ {{cond}} → Just (record
      { tip = tip w
      ; finality = newFinality
      ; invariant = projr (prop-&&-⋀ cond)
      }))
    else Nothing

{-# FOREIGN AGDA2HS
  -- | Intersection of two 'RollbackWindow'.
#-}
-- The anonymous module is need to get `forall time` in the Haskell code.
module _ {time : Set} {{_ : Ord time}} where
  intersection
    : ∀ {{@0 _ : IsLawfulOrd time}}
    → RollbackWindow time → RollbackWindow time → Maybe (RollbackWindow time)
  intersection w1 w2 =
    if' (fin3 <= tip3)
      (λ eq → Just (record
          { tip = tip3
          ; finality = fin3
          ; invariant = eq
          })
      )
      (λ eq → Nothing)
    where
      fin3 = max (finality w1) (finality w2)
      tip3 = min (tip w1) (tip w2)

{-# COMPILE AGDA2HS RollbackWindow #-}
{-# COMPILE AGDA2HS member #-}
{-# COMPILE AGDA2HS singleton #-}
{-# COMPILE AGDA2HS rollForward #-}
{-# COMPILE AGDA2HS MaybeRollback #-}
{-# COMPILE AGDA2HS rollBackward #-}
{-# COMPILE AGDA2HS prune #-}
{-# COMPILE AGDA2HS intersection #-}

{-----------------------------------------------------------------------------
    Properties
    Simple
------------------------------------------------------------------------------}
-- |
-- The 'tip' is always a 'member' of a 'RollbackWindow'.
@0 prop-member-tip
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (w : RollbackWindow time)
  → member (tip w) w ≡ True
--
prop-member-tip w =
  begin
    member (tip w) w
  ≡⟨⟩
    (finality w <= tip w) && (tip w <= tip w)
  ≡⟨ cong (λ o → (finality w <= tip w) && o) (reflexivity (tip w)) ⟩
    (finality w <= tip w) && True
  ≡⟨ prop-x-&&-True _ ⟩
    (finality w <= tip w)
  ≡⟨ invariant w ⟩
    True
  ∎

-- |
-- The 'finality' is always a 'member' of a 'RollbackWindow'.
@0 prop-member-finality
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (w : RollbackWindow time)
  → member (finality w) w ≡ True
--
prop-member-finality w =
  begin
    member (finality w) w
  ≡⟨⟩
    (finality w <= finality w) && (finality w <= tip w)
  ≡⟨ cong (λ o → o && (finality w <= tip w) ) (reflexivity (finality w)) ⟩
    True && (finality w <= tip w)
  ≡⟨ invariant w ⟩
    True
  ∎

--
lemma-antisymmetry
  : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → ((x <= y) && (y <= x)) ≡ (x == y)
--
lemma-antisymmetry x y
  rewrite lte2LtEq x y
    | lte2gte y x
    | gte2GtEq x y
    | compareLt x y
    | compareGt x y
    | compareEq x y
    with compare x y
... | GT = refl 
... | EQ = refl 
... | LT = refl

-- |
-- 'singleton' contains exactly one point.
@0 prop-member-singleton
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (t1 t2 : time)
  → member t1 (singleton t2) ≡ (t1 == t2)
--
prop-member-singleton t1 t2 =
  begin
    (t2 <= t1) && (t1 <= t2)
  ≡⟨ lemma-antisymmetry t2 t1 ⟩
    t2 == t1
  ≡⟨ eqSymmetry t2 t1 ⟩
    t1 == t2
  ∎

{-----------------------------------------------------------------------------
    Properties
    Contrapositives
------------------------------------------------------------------------------}
--
@0 prop-isJust-rollForward
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (newTip : time) (w : RollbackWindow time)
  → isJust (rollForward newTip w) ≡ (tip w < newTip)
--
prop-isJust-rollForward newTip w =
  case (tip w < newTip) of λ
    { True {{eq}} →
      begin
        isJust (rollForward newTip w)
      ≡⟨ cong isJust (prop-if'-True eq) ⟩
        True
      ≡⟨ sym eq ⟩
        tip w < newTip
      ∎
    ; False {{eq}} →
      begin
        isJust (rollForward newTip w)
      ≡⟨ cong isJust (prop-if'-False eq) ⟩
        False
      ≡⟨ sym eq ⟩
        tip w < newTip
      ∎
    }

--
postulate
 prop-tip-rollForward
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (newTip : time) (w w' : RollbackWindow time)
  → rollForward newTip w ≡ Just w'
  → tip w' ≡ newTip
--

--
@0 prop-rollBackward-Future→tip
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (newTip : time) (w : RollbackWindow time)
  → rollBackward newTip w ≡ Future
  → (tip w <= newTip) ≡ True
--
prop-rollBackward-Future→tip newTip w eq0 =
  case (tip w <= newTip) of λ
    { True {{eqTip}} → eqTip
    ; False {{eqTip}} → case (finality w <= newTip) of λ
      { True {{eqFin}} →
        case trans (sym (eq0)) (trans (prop-if'-False eqTip) (prop-if'-True eqFin)) of λ ()
      ; False {{eqFin}} →
        case trans (sym (eq0)) (trans (prop-if'-False eqTip) (prop-if'-False eqFin)) of λ ()
      }
    }

--
postulate
 prop-rollBackward-tip→Future
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (newTip : time) (w : RollbackWindow time)
  → (tip w <= newTip) ≡ True
  → rollBackward newTip w ≡ Future
--

{-----------------------------------------------------------------------------
    Properties
    intersection
------------------------------------------------------------------------------}
--
@0 lemma-between-max-min
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
  → (t1 t2 t3 t4 t : time)
  → ((max t1 t2 <= t) && (t <= min t3 t4))
    ≡ ((t1 <= t && t <= t3) && (t2 <= t && t <= t4))
--
lemma-between-max-min t1 t2 t3 t4 t =
    begin
      max t1 t2 <= t && t <= min t3 t4
    ≡⟨ cong (λ o → o && t <= min t3 t4) (prop-max-universal t1 t2 t) ⟩
      (t1 <= t && t2 <= t) && (t <= min t3 t4)
    ≡⟨ cong (λ o → (t1 <= t && t2 <= t) && o) (prop-min-universal t t3 t4) ⟩
      (t1 <= t && t2 <= t) && (t <= t3 && t <= t4)
    ≡⟨ shuffle (t1 <= t) (t2 <= t) (t <= t3) (t <= t4) ⟩
      ((t1 <= t && t <= t3) && (t2 <= t && t <= t4))
    ∎
  where
    shuffle
      : ∀ (b1 b2 b3 b4 : Bool)
      → ((b1 && b2) && (b3 && b4))
        ≡ ((b1 && b3) && (b2 && b4))
    shuffle False b2 b3 b4 = refl
    shuffle True False False b4 = refl
    shuffle True False True b4 = refl
    shuffle True True b3 b4 = refl

-- |
-- A time @t@ is a 'member' of an intersection
-- if it is a member of both 'RollbackWindow's.
@0 prop-member-intersection
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (w1 w2 w3 : RollbackWindow time)
      (t : time)
  → intersection w1 w2 ≡ Just w3
  → member t w3 ≡ (member t w1 && member t w2)
--
prop-member-intersection w1 w2 w3 t eq0 =
    begin
      member t w3
    ≡⟨⟩
      (finality w3 <= t) && (t <= tip w3)
    ≡⟨ cong (λ o → (o <= t) && _) eqFin ⟩
      (fin3 <= t) && (t <= tip w3)
    ≡⟨ cong (λ o → (fin3 <= t) && (t <= o)) eqTip ⟩
      (fin3 <= t) && (t <= tip3)
    ≡⟨ lemma-between-max-min (finality w1) (finality w2) (tip w1) (tip w2) t ⟩
      (member t w1 && member t w2)
    ∎
  where
    fin3 = max (finality w1) (finality w2)
    tip3 = min (tip w1) (tip w2)

    @0 cases
      : (b : Bool) → (@0 cond : (fin3 <= tip3) ≡ b) → (fin3 <= tip3) ≡ True
    cases True cond = cond
    cases False cond = case trans (sym eqNothing) eq0 of λ ()
      where
        eqNothing =
          begin
            intersection w1 w2
          ≡⟨⟩
            if' (fin3 <= tip3) _ (λ eq → Nothing)
          ≡⟨ prop-if'-False cond ⟩
            Nothing
          ∎

    contra
      : (fin3 <= tip3) ≡ True
    contra = case (fin3 <= tip3) of λ
      { True {{cond}} → cases True cond
      ; False {{cond}} → cases False cond
      }

    eqJust =
      begin
        Just w3
      ≡⟨ sym eq0 ⟩
        intersection w1 w2
      ≡⟨ prop-if'-True contra ⟩
        Just (record
          { tip = tip3
          ; finality = fin3
          ; invariant = contra
          })
      ∎

    eqFin : finality w3 ≡ fin3
    eqFin = cong finality (prop-Just-injective _ _ eqJust)

    eqTip : tip w3 ≡ tip3
    eqTip = cong tip (prop-Just-injective _ _ eqJust)
