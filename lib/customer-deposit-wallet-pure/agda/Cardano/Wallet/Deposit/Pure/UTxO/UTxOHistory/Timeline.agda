-- |
-- Implementation of 'TimelineUTxO'.
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Timeline
    {-|
      -- * TimelineUTxO
    ; TimelineUTxO (..)
    ; getUTxO
    ; fromOrigin

      -- * Operations
    ; insertDeltaUTxO
    ; dropAfter
      ; prop-insertDeltaUTxO-dropAfter-cancel
    ; pruneBefore

      -- * Internal
    ; getSpent
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO using
    ( DeltaUTxO
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    ; dom
    ; excluding
    ; _⋪_
    ; _⊲_
    ; _∪_
    )
open import Cardano.Wallet.Read using
    ( Slot
    ; SlotNo
    ; TxIn
    ; WithOrigin
    )
open import Data.Maps.Timeline using
    ( Timeline
    )
open import Data.Map using
    ( Map
    )
open import Data.Set using
    ( ℙ
    )

import Cardano.Wallet.Deposit.Pure.RollbackWindow as RollbackWindow
import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO as DeltaUTxO
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Data.Maps.Timeline as Timeline
import Data.Map as Map
import Data.Set as Set

{-# FOREIGN AGDA2HS
{-# LANGUAGE StrictData #-}
#-}

{-----------------------------------------------------------------------------
    Type
------------------------------------------------------------------------------}

-- | 'TimelineUTxO' represents a timeline of changes to an initial 'UTxO' set.
--
-- This data type is useful for keeping track of a 'UTxO' set that
-- can be rolled forward and backward in time.
--
-- We keep track of the creation
-- and spending of slot of each 'TxIn'.
-- This allows us to rollback to a given slot
-- and prune to a given slot.
--
-- * 'history' — Transaction outputs in the history, both spent and unspent.
-- * 'created' — Creation slots of all 'TxIn' present in the 'history'.
-- * 'spent' — Spending slots for those 'TxIn' that have been spent.
-- * 'boot' — Transaction outputs that were created at genesis.
record TimelineUTxO : Set where
  field
    history : UTxO
    created : Timeline Slot TxIn
    spent : Timeline SlotNo TxIn
    boot : UTxO

open TimelineUTxO public

{-# COMPILE AGDA2HS TimelineUTxO #-}

{-----------------------------------------------------------------------------
    Functions
------------------------------------------------------------------------------}

-- | Current 'UTxO' at the end of the timeline,
-- obtained by applying all changes in the timeline.
getUTxO : TimelineUTxO → UTxO
getUTxO us = excluding (history us) (Timeline.items (spent us))

{-# COMPILE AGDA2HS getUTxO #-}

-- | The spent 'TxIn's that can be rolled back.
--
-- (Internal, exported for specification.)
getSpent : TimelineUTxO → Map TxIn SlotNo
getSpent = Timeline.getMapTime ∘ spent

{-# COMPILE AGDA2HS getSpent #-}

-- | A 'TimelineUTxO' created from an initial 'UTxO' at genesis.
fromOrigin : UTxO → TimelineUTxO
fromOrigin utxo = record
    { history = utxo
    ; created =
        Timeline.insertMany WithOrigin.Origin (dom utxo) (Timeline.empty)
    ; spent = Timeline.empty
    ; boot = utxo
    }

{-# COMPILE AGDA2HS fromOrigin #-}

-- | Change the 'history' at a given slot by applying a 'DeltaUTxO'.
--
-- This action will
--
-- * add the 'received' transaction outputs from the delta
--   to the 'history' and the 'created' collections,
-- * add the 'excluded' inpts to the 'spent' collection.
--
-- In order for this operation to make sense,
-- we typically need to assume that the 'DeltaUTxO' 'fit's the 'history'.
insertDeltaUTxO
  : SlotNo → DeltaUTxO → TimelineUTxO → TimelineUTxO
insertDeltaUTxO newTip delta old = record
    { history =
        UTxO.union (history old) (DeltaUTxO.received delta)
    ; created =
        Timeline.insertMany
            (WithOrigin.At newTip) receivedTxIns (created old)
    ; spent =
        Timeline.insertMany
            newTip excludedTxIns (spent old)
    ; boot = boot old
    }
  where
    receivedTxIns =
        Set.difference
            (dom (DeltaUTxO.received delta))
            (dom (history old))
    excludedTxIns =
        Set.difference
            (Set.intersection (DeltaUTxO.excluded delta) (dom (history old)))
            (Timeline.items (spent old))

{-# COMPILE AGDA2HS insertDeltaUTxO #-}

-- | Helper for 'dropAfter'.
dropAfterSpent
  : Slot → Timeline.Timeline SlotNo TxIn → Timeline.Timeline SlotNo TxIn
dropAfterSpent WithOrigin.Origin spents = Timeline.empty
dropAfterSpent (WithOrigin.At slot) spents = Timeline.dropAfter slot spents

-- | Drop all changes recored in the timeline after a given slot.
dropAfter
  : Slot → TimelineUTxO → TimelineUTxO
dropAfter newTip old = record
    { history = excluding (history old) rolledCreated
    ; created = created'
    ; spent = dropAfterSpent newTip (spent old)
    ; boot = boot old
    }
  where
    deletedAfter = Timeline.deleteAfter newTip (created old)
    rolledCreated = fst deletedAfter
    created' = snd deletedAfter

{-# COMPILE AGDA2HS dropAfterSpent #-}
{-# COMPILE AGDA2HS dropAfter #-}

{-|
Combine all changes before the given 'SlotNo'.

Using 'prune' will free up some space as old information
can be summarized and discarded.
-}
pruneBefore : SlotNo → TimelineUTxO → TimelineUTxO
pruneBefore newFinality old = record
    { history = excluding (history old) prunedTxIns
    ; created = Timeline.difference (created old) prunedTxIns
    ; spent = spent1
    ; boot = boot old
    }
  where
    pruned = Timeline.dropWhileAntitone (_<= newFinality) (spent old)
    prunedTxIns = fst pruned
    spent1 = snd pruned

{-# COMPILE AGDA2HS pruneBefore #-}

{-----------------------------------------------------------------------------
    Properties
    Helpers
------------------------------------------------------------------------------}
--
lemma-equality-TimelineUTxO
  : ∀ (u1 u2 : TimelineUTxO)
  → TimelineUTxO.history u1 ≡ TimelineUTxO.history u2
  → TimelineUTxO.created u1 ≡ TimelineUTxO.created u2
  → TimelineUTxO.spent u1 ≡ TimelineUTxO.spent u2
  → TimelineUTxO.boot u1 ≡ TimelineUTxO.boot u2
  → u1 ≡ u2
--
lemma-equality-TimelineUTxO u1 u2 refl refl refl refl = refl

--
lemma-WithOrigin-At-monotonic
  : ∀ (x y : SlotNo)
  → (WithOrigin.At x < WithOrigin.At y) ≡ (x < y)
--
lemma-WithOrigin-At-monotonic x y = refl

--
@0 lemma-UTxO-difference
  : ∀ (x y : UTxO)
  → ((Set.difference (dom x) (dom y)) ⋪ (y ∪ x))
    ≡ y
--
lemma-UTxO-difference x y =
  begin
    ((Set.difference (dom x) (dom y)) ⋪ (y ∪ x))
  ≡⟨ UTxO.prop-excluding-difference ⟩
    (dom x ⋪ (y ∪ x)) ∪ (dom y ⊲ (y ∪ x))
  ≡⟨ cong (λ o → o ∪ expr1) UTxO.prop-excluding-union ⟩
    ((dom x ⋪ y) ∪ (dom x ⋪ x)) ∪ expr1
  ≡⟨ cong (λ o → ((dom x ⋪ y) ∪ o) ∪ expr1) (UTxO.prop-excluding-dom {x}) ⟩
    ((dom x ⋪ y) ∪ UTxO.empty) ∪ expr1
  ≡⟨ cong (λ o → o ∪ expr1) (UTxO.prop-union-empty-right {dom x ⋪ y}) ⟩
    (dom x ⋪ y) ∪ (dom y ⊲ (y ∪ x))
  ≡⟨ cong (λ o → expr2 ∪ o) (UTxO.prop-restrictedBy-union {dom y} {y} {x}) ⟩
    expr2 ∪ ((dom y ⊲ y) ∪ (dom y ⊲ x))
  ≡⟨ cong (λ o → expr2 ∪ (o ∪ (dom y ⊲ x))) UTxO.prop-restrictedBy-dom ⟩
    (dom x ⋪ y) ∪ (y ∪ (dom y ⊲ x)) 
  ≡⟨ sym UTxO.prop-union-assoc ⟩
    ((dom x ⋪ y) ∪ y) ∪ (dom y ⊲ x)
  ≡⟨ cong (λ o → o ∪ (dom y ⊲ x)) UTxO.prop-excluding-absorb ⟩
    y ∪ (dom y ⊲ x)
  ≡⟨ UTxO.prop-union-restrictedBy-absorbs ⟩
    y
  ∎
 where
  expr1 = dom y ⊲ (y ∪ x)
  expr2 = dom x ⋪ y

{-----------------------------------------------------------------------------
    Properties
    getUTxO
------------------------------------------------------------------------------}
-- | Rolling forward updates the 'UTxO'.
postulate
 prop-getUTxO-insertDeltaUTxO
  : ∀ (u : TimelineUTxO) (du : DeltaUTxO) (slot : SlotNo)
  → DeltaUTxO.fits du (history u) ≡ True
  → getUTxO (insertDeltaUTxO slot du u)
    ≡ DeltaUTxO.apply du (getUTxO u)

{-----------------------------------------------------------------------------
    Properties
    Cancellation
------------------------------------------------------------------------------}

-- | Rolling backward will cancel rolling forward.
@0 prop-insertDeltaUTxO-dropAfter-cancel
  : ∀ (u : TimelineUTxO) (du : DeltaUTxO) (slot1 : Slot) (slot2 : SlotNo)
  → (slot1 < WithOrigin.At slot2) ≡ True
  → dropAfter slot1 (insertDeltaUTxO slot2 du u)
    ≡ dropAfter slot1 u
--
prop-insertDeltaUTxO-dropAfter-cancel u du slot1 slot2 cond =
    lemma-equality-TimelineUTxO u1 u2
      lemHistory
      (Timeline.prop-dropAfter-insertMany slot1 (WithOrigin.At slot2) _ (created u) cond)
      lemSpent
      refl
  where
    u1 = dropAfter slot1 (insertDeltaUTxO slot2 du u)
    u2 = dropAfter slot1 u

    txs1 = fst (Timeline.deleteAfter slot1 (created (insertDeltaUTxO slot2 du u)))
    txs2 = fst (Timeline.deleteAfter slot1 (created u))
    receivedTxIns =
        Set.difference
            (dom (DeltaUTxO.received du))
            (dom (history u))

    lemTxs : txs1 ≡ Set.union txs2 receivedTxIns
    lemTxs = Timeline.prop-deleteAfter-insertMany slot1 (WithOrigin.At slot2) receivedTxIns (created u) cond

    lemReceivedTxIns
      : (receivedTxIns ⋪ (history u ∪ DeltaUTxO.received du))
        ≡ history u
    lemReceivedTxIns =
      lemma-UTxO-difference (DeltaUTxO.received du) (history u)

    lemHistory : history u1 ≡ history u2
    lemHistory =
      begin
        history u1
      ≡⟨⟩
        txs1 ⋪ (history u ∪ DeltaUTxO.received du)
      ≡⟨ cong (λ o → o ⋪ _) lemTxs ⟩
        (Set.union txs2 receivedTxIns) ⋪ (history u ∪ DeltaUTxO.received du)
      ≡⟨ sym (UTxO.prop-excluding-excluding {txs2} {receivedTxIns} {history u ∪ DeltaUTxO.received du}) ⟩
        (txs2 ⋪ (receivedTxIns ⋪ (history u ∪ DeltaUTxO.received du)))
      ≡⟨ cong (λ o → txs2 ⋪ o) lemReceivedTxIns ⟩
        (txs2 ⋪ history u)
      ≡⟨⟩
        history u2
      ∎

    lemSpent : TimelineUTxO.spent u1 ≡ TimelineUTxO.spent u2
    lemSpent = case slot1 of λ
      { WithOrigin.Origin {{eq}} →
        begin
          TimelineUTxO.spent u1
        ≡⟨⟩
          dropAfterSpent slot1 (TimelineUTxO.spent (insertDeltaUTxO slot2 du u))
        ≡⟨ cong (λ o → dropAfterSpent o _) eq ⟩
          Timeline.empty
        ≡⟨ sym (cong (λ o → dropAfterSpent o _) eq) ⟩
          TimelineUTxO.spent u2
        ∎
      ; (WithOrigin.At slot) {{eq}} →
        begin
          TimelineUTxO.spent u1
        ≡⟨⟩
          dropAfterSpent slot1 (TimelineUTxO.spent (insertDeltaUTxO slot2 du u))
        ≡⟨ cong (λ o → dropAfterSpent o _) eq ⟩
          Timeline.dropAfter slot (TimelineUTxO.spent (insertDeltaUTxO slot2 du u))
        ≡⟨ Timeline.prop-dropAfter-insertMany slot slot2 _ (TimelineUTxO.spent u) (trans (sym (lemma-WithOrigin-At-monotonic slot slot2)) (subst (λ o → (o < WithOrigin.At slot2) ≡ True) eq cond)) ⟩
          Timeline.dropAfter slot (TimelineUTxO.spent u)
        ≡⟨ sym (cong (λ o → dropAfterSpent o _) eq) ⟩
          TimelineUTxO.spent u2
        ∎
      }

