{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.RollbackWindow where

open import Haskell.Prelude hiding
    ( null
    )
open import Haskell.Reasoning

open import Haskell.Data.Maybe using
    ( prop-Just-injective
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
  : ∀ (b : Bool)
  → (cond : b ≡ False)
  → {thn : @0 (b ≡ True) → a}
  → {els : @0 (b ≡ False) → a}
  → if' b thn els ≡ els cond
prop-if'-False .False refl = refl

prop-if'-True
  : ∀ (b : Bool)
  → (cond : b ≡ True)
  → {thn : @0 (b ≡ True) → a}
  → {els : @0 (b ≡ False) → a}
  → if' b thn els ≡ thn cond
prop-if'-True .True refl = refl

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
-- The 'tip' is the higher end of the interval,
-- representing the latest state of the data.
-- The 'finality' is the lower end of the interval,
-- until which rollbacks are supported.
record RollbackWindow (time : Set) {{@0 _ : Ord time}} : Set where
  constructor RollbackWindowC
  field
    finality : time
    tip : time
    @0 invariant : (finality <= tip) ≡ True

open RollbackWindow public

-- | Test whether a given time is within a 'RollbackWindow'.
member
    : ∀ {time} {{_ : Ord time}}
    → time → RollbackWindow time → Bool
member time w = (finality w <= time) && (time <= tip w)

-- | Interval containing a single point
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
    if tip w < newTip
       then (λ {{cond}} → Just (record
          { finality = finality w
          ; tip = newTip
          ; invariant =
            transitivity
              (finality w) (tip w) newTip
              (prop-⋀-&& (invariant w `and` (lt2lte (tip w) newTip cond)))
          }))
       else Nothing

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
  if tip w < newTip
    then Future
    else if finality w <= newTip
      then (λ {{cond}} → Present (record
        { tip = newTip
        ; finality = finality w
        ; invariant = cond
        }))
      else Past

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
  intersect
    : ∀ {{@0 _ : IsLawfulOrd time}}
    → RollbackWindow time → RollbackWindow time → Maybe (RollbackWindow time)
  intersect w1 w2 =
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
{-# COMPILE AGDA2HS intersect #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- |
-- The 'tip' is always a 'member' of a 'RollbackWindow'.
@0 prop-tip-member
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (w : RollbackWindow time)
  → member (tip w) w ≡ True
--
prop-tip-member w =
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
@0 prop-finality-member
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (w : RollbackWindow time)
  → member (finality w) w ≡ True
--
prop-finality-member w =
  begin
    member (finality w) w
  ≡⟨⟩
    (finality w <= finality w) && (finality w <= tip w)
  ≡⟨ cong (λ o → o && (finality w <= tip w) ) (reflexivity (finality w)) ⟩
    True && (finality w <= tip w)
  ≡⟨ invariant w ⟩
    True
  ∎

{-
Remark: 
Somehow, we want to make an argument based on the result of a function.
"If it returns Just, then some precondition has to hold".
I think that this is a regularly occuring pattern which we need to
handle better than this, where we undo the structure of the function.
Somehow, taking the contrapositive is very classical reasoning.
-}

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
@0 prop-member-intersect
  : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
      (w1 w2 w3 : RollbackWindow time)
      (t : time)
  → intersect w1 w2 ≡ Just w3
  → member t w3 ≡ (member t w1 && member t w2)
--
prop-member-intersect w1 w2 w3 t eq0 =
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
            intersect w1 w2
          ≡⟨⟩
            if' (fin3 <= tip3) _ (λ eq → Nothing)
          ≡⟨ prop-if'-False (fin3 <= tip3) cond ⟩
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
        intersect w1 w2
      ≡⟨⟩
        if' (fin3 <= tip3)
          (λ eq → Just (record
            { tip = tip3
            ; finality = fin3
            ; invariant = eq
            })
          )
          (λ eq → Nothing)
      ≡⟨ prop-if'-True (fin3 <= tip3) contra ⟩
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
