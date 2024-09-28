{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    {-
    ; DeltaUTxO
      ; null
      ; empty
      ; apply
      ; excludingD
      ; receiveD
      ; instance Semigroup DeltaUTxO
      ; instance Monoid DeltaUTxO
    -}
    where

open import Haskell.Prelude hiding
    ( null
    ; concat
    )
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
      ; dom
      ; _∪_
      ; _⋪_
    )
open import Cardano.Wallet.Read using
    ( TxIn
    )
open import Haskell.Data.Set using
    ( ℙ
    )

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    DeltaUTxO
------------------------------------------------------------------------------}
-- | Representation of a change (delta) to a 'UTxO'.
--
-- The delta records inputs that are excluded, and outputs that are added.
record DeltaUTxO : Set where
  field
    excluded : Set.ℙ TxIn
    received : UTxO

open DeltaUTxO public

postulate
  instance
    iShowDeltaUTxO : Show DeltaUTxO

{-# COMPILE AGDA2HS iShowDeltaUTxO derive #-}

-- | Test efficiently whether the change does nothing.
null : DeltaUTxO → Bool
null du = Set.null (excluded du) && UTxO.null (received du)

-- | The empty change does nothing.
empty : DeltaUTxO
empty = record
  { excluded = Set.empty
  ; received = Map.empty
  }

-- | Apply a change to a 'UTxO'.
apply : DeltaUTxO → UTxO → UTxO
apply du utxo =
   UTxO.union (received du) (UTxO.excluding utxo (excluded du))

-- | Variant of 'excluding' that also returns a delta.
excludingD : UTxO → Set.ℙ TxIn → (DeltaUTxO × UTxO)
excludingD utxo txins =
    (du , UTxO.excluding utxo txins)
  where
    du = record
      { excluded = Set.intersection txins (dom utxo)
      ; received = UTxO.empty
      }

-- | Variant of 'union' that also returns a delta.
-- The first argument is the 'UTxO' on which the delta acts.
--
-- > receiveD old new
receiveD : UTxO → UTxO → (DeltaUTxO × UTxO)
receiveD old new =
    (du , UTxO.union new old)
  where
    du = record 
      { excluded = Set.empty
      ; received = new
      }

-- | Combine two deltas: Apply @x@ /after/ applying @y@.
-- Drops inputs that were created by @y@, but removed again by @x@
append : DeltaUTxO → DeltaUTxO → DeltaUTxO
append x y = record
    { excluded = Set.union (excluded'x) (excluded y)
    ; received = UTxO.union (received x) (received'y)
    }
  where
    excluded'x = UTxO.excludingS (excluded x) (received y)
    received'y = UTxO.excluding (received y) (excluded x)

-- | Combine a sequence of 'DeltaUTxO' using `append`
concat : List DeltaUTxO → DeltaUTxO
concat = foldr append empty

{-# COMPILE AGDA2HS DeltaUTxO #-}
{-# COMPILE AGDA2HS null #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS apply #-}
{-# COMPILE AGDA2HS excludingD #-}
{-# COMPILE AGDA2HS receiveD #-}
{-# COMPILE AGDA2HS append #-}
{-# COMPILE AGDA2HS concat #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
lemma-intro-DeltaUTxO-≡
  : ∀ {a : Set.ℙ TxIn} {b : UTxO} (dd : DeltaUTxO)
  → excluded dd ≡ a
  → received dd ≡ b
  → dd ≡ record { excluded = a; received = b }
lemma-intro-DeltaUTxO-≡ dd refl refl = refl

--
prop-null-empty
  : ∀ (du : DeltaUTxO)
  → null du ≡ True
  → du ≡ empty
--
prop-null-empty du eq =
    lemma-intro-DeltaUTxO-≡
      du
      (Set.prop-null-empty (excluded du) lem1)
      (Map.prop-null-empty (received du) lem2)
  where
    lem1 : Set.null (excluded du) ≡ True
    lem1 = projl (prop-&&-⋀ eq)

    lem2 : Map.null (received du) ≡ True
    lem2 = projr (prop-&&-⋀ eq)

--
@0 prop-apply-empty
  : ∀ (utxo : UTxO)
  → apply empty utxo ≡ utxo
--
prop-apply-empty utxo =
  begin
    apply empty utxo
  ≡⟨ UTxO.prop-union-empty-left ⟩
    UTxO.excluding utxo (excluded empty)
  ≡⟨ UTxO.prop-excluding-empty utxo ⟩
    utxo
  ∎

--
@0 lemma-excluding-intersection-dom
  : ∀ {x : Set.ℙ TxIn} {utxo : UTxO}
  → (Set.intersection x (dom utxo)) ⋪ utxo ≡ x ⋪ utxo
--
lemma-excluding-intersection-dom {x} {utxo} =
  begin
    (Set.intersection x (dom utxo)) ⋪ utxo
  ≡⟨ UTxO.prop-excluding-intersection ⟩
    (x ⋪ utxo) ∪ (dom utxo ⋪ utxo)
  ≡⟨ cong (λ o → (x ⋪ utxo) ∪ o) UTxO.prop-excluding-dom ⟩
    (x ⋪ utxo) ∪ UTxO.empty
  ≡⟨ UTxO.prop-union-empty-right ⟩
    (x ⋪ utxo)
  ∎

-- | The 'UTxO' returned by 'excludingD' is the same as 'excluding'.
--
prop-excluding-excludingD
  : ∀ {txins : Set.ℙ TxIn} {u0 : UTxO}
  → let (du , u1) = excludingD u0 txins
    in  u1 ≡ UTxO.excluding u0 txins
--
prop-excluding-excludingD {txins} {u0} = refl

-- | Applying the 'DeltaUTxO' returned by 'excludingD'
-- to the argument 'UTxO' yields the result 'UTxO'.
--
@0 prop-apply-excludingD
  : ∀ {txins : Set.ℙ TxIn} {u0 : UTxO}
  → let (du , u1) = excludingD u0 txins
    in  apply du u0 ≡ u1
--
prop-apply-excludingD {txins} {u0} =
  begin
    apply du u0
  ≡⟨⟩
    (received du) ∪ (excluded du ⋪ u0)
  ≡⟨ UTxO.prop-union-empty-left ⟩
    excluded du ⋪ u0
  ≡⟨⟩
    Set.intersection txins (dom u0) ⋪ u0
  ≡⟨ lemma-excluding-intersection-dom ⟩
    txins ⋪ u0
  ≡⟨⟩
    u1
  ∎
  where
    du = fst (excludingD u0 txins)
    u1 = snd (excludingD u0 txins)

-- | The 'UTxO' returned by 'receiveD' is obtained by 'union'.
--
prop-union-receiveD
  : ∀ {ua : UTxO} {u0 : UTxO}
  → let (du , u1) = receiveD u0 ua
    in  u1 ≡ UTxO.union ua u0
--
prop-union-receiveD {ua} {u0} = refl

-- | Applying the 'DeltaUTxO' returned by 'receiveD'
-- to the argument 'UTxO' yields the result 'UTxO'.
--
@0 prop-apply-receiveD
  : ∀ {ua : UTxO} {u0 : UTxO}
  → let (du , u1) = receiveD u0 ua
    in  apply du u0 ≡ u1
--
prop-apply-receiveD {ua} {u0} =
  begin
    apply du u0
  ≡⟨⟩
    (received du) ∪ (excluded du ⋪ u0)
  ≡⟨ cong (λ o → received du ∪ o) (UTxO.prop-excluding-empty _) ⟩
    (received du) ∪ u0
  ≡⟨⟩
    u1
  ∎
  where
    du = fst (receiveD u0 ua)
    u1 = snd (receiveD u0 ua)

--
-- This is the most important property:
-- The semigroup operation `_<>_` is an application of `apply`.
prop-apply-append
  : ∀ (x y : DeltaUTxO) (utxo : UTxO)
  → Set.intersection (dom (received y)) (dom utxo) ≡ Set.empty
  → apply (append x y) utxo ≡ apply x (apply y utxo)
prop-apply-append x y utxo cond =
    begin
      apply (append x y) utxo
    ≡⟨⟩
      received (append x y) ∪ (excluded (append x y) ⋪ utxo)
    ≡⟨⟩
      (received x ∪ (excluded x ⋪ received y))
        ∪ (excluded (append x y) ⋪ utxo)
    ≡⟨ UTxO.prop-union-assoc ⟩
      received x ∪ ((excluded x ⋪ received y)
        ∪ (excluded (append x y) ⋪ utxo))
    ≡⟨ cong (λ o → received x ∪ ((excluded x ⋪ received y) ∪ o)) lem1 ⟩
      received x ∪ ((excluded x ⋪ received y)
        ∪ (excluded x ⋪ (excluded y ⋪ utxo)))
    ≡⟨ cong (λ o → received x ∪ o) (sym (UTxO.prop-excluding-union (excluded x) _ _)) ⟩
      received x ∪ (excluded x ⋪ (received y ∪ (excluded y ⋪ utxo)))
    ≡⟨⟩
      apply x (received y ∪ (excluded y ⋪ utxo))
    ≡⟨⟩
      apply x (apply y utxo)
    ∎
  where
    lem1 =
      begin
        excluded (append x y) ⋪ utxo
      ≡⟨⟩
        Set.union (UTxO.excludingS (excluded x) (received y)) (excluded y) ⋪ utxo
      ≡⟨ cong (λ o → o ⋪ utxo) Set.prop-union-sym ⟩
        Set.union (excluded y) (UTxO.excludingS (excluded x) (received y)) ⋪ utxo
      ≡⟨ sym UTxO.prop-excluding-excluding ⟩
        excluded y ⋪ (UTxO.excludingS (excluded x) (received y) ⋪ utxo)
      ≡⟨ cong (λ o → excluded y ⋪ o) (UTxO.prop-excluding-excludingS cond) ⟩
        excluded y ⋪ (excluded x ⋪ utxo)
      ≡⟨ UTxO.prop-excluding-sym ⟩
        excluded x ⋪ (excluded y ⋪ utxo)
      ∎

--
-- Unit test for 'concat'.
prop-concat-two
  : ∀ (x y : DeltaUTxO)
  → concat (x ∷ y ∷ []) ≡ append x (append y empty)
--
prop-concat-two x y = refl
