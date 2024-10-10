-- |
-- 'UTxOHistory' represents a history of a UTxO set that can be rolled
-- back (up to the 'finality' point).
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core
    {-|
      -- * UTxOHistory
    ; UTxOHistory (..)

    ; empty
    ; getUTxO
    ; getRollbackWindow
      ; getTip

      -- * Operations
    ; DeltaUTxOHistory (..)
    ; applyDeltaUTxOHistory
    ; rollForward
      ; prop-rollForward-present
    ; rollBackward
      ; prop-rollBackward-tip
      ; prop-rollBackward-future
      ; prop-rollBackward-rollForward-cancel
      ; prop-rollBackward-tip-rollForward
    ; prune

      -- * Internal
    ; getSpent
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO using
    ( DeltaUTxO
    )
open import Cardano.Wallet.Deposit.Pure.RollbackWindow using
    ( RollbackWindow
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    ; dom
    ; excluding
    ; _⋪_
    ; _⊲_
    ; _∪_
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type using
    ( UTxOHistory
    )
open import Cardano.Wallet.Read using
    ( Slot
    ; SlotNo
    ; TxIn
    ; WithOrigin
    )
open import Haskell.Data.List using
    ( foldl'
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Maybe using
    ( isJust
    )
open import Haskell.Data.Set using
    ( ℙ
    )

import Cardano.Wallet.Deposit.Pure.RollbackWindow as RollbackWindow
import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO as DeltaUTxO
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Haskell.Data.Map as Map
import Haskell.Data.Maps.Timeline as Timeline
import Haskell.Data.Set as Set

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type
    ( UTxOHistory (..)
    )
#-}

{-----------------------------------------------------------------------------
    Helper stuff
------------------------------------------------------------------------------}

variable
  key v : Set

{-----------------------------------------------------------------------------
    Basic functions
------------------------------------------------------------------------------}

-- | An empty UTxO history
empty : UTxO → UTxOHistory
empty utxo =
    record
        { history = utxo
        ; created =
            Timeline.insertMany WithOrigin.Origin (dom utxo)
            (Timeline.empty)
        ; spent = Timeline.empty
        ; window = RollbackWindow.singleton WithOrigin.Origin
        ; boot = utxo
        }

-- | UTxO at the tip of history.
getUTxO : UTxOHistory → UTxO
getUTxO us =
    excluding history (Map.keysSet (Timeline.getMapTime spent))
  where
    open UTxOHistory us

-- | 'RollbackWindow' within which we can roll back.
--
-- The tip of the history is also the upper end of this window.
-- The UTxO history includes information from all blocks
-- between genesis and the tip, and including the block at the tip.
getRollbackWindow : UTxOHistory → RollbackWindow.RollbackWindow Slot
getRollbackWindow x = UTxOHistory.window x

-- | Tip of the 'UTxOHistory'.
getTip : UTxOHistory → Slot
getTip = RollbackWindow.tip ∘ getRollbackWindow

-- | The spent 'TxIn's that can be rolled back.
--
-- (Internal, exported for specification.)
getSpent : UTxOHistory → Map TxIn SlotNo
getSpent = Timeline.getMapTime ∘ UTxOHistory.spent

{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS getUTxO #-}
{-# COMPILE AGDA2HS getRollbackWindow #-}
{-# COMPILE AGDA2HS getTip #-}
{-# COMPILE AGDA2HS getSpent #-}

{-----------------------------------------------------------------------------
    DeltaUTxOHistory
------------------------------------------------------------------------------}

-- | Representation of a change (delta) to a 'UTxOHistory'.
data DeltaUTxOHistory : Set where
    AppendBlock : SlotNo → DeltaUTxO → DeltaUTxOHistory
        -- ^ New slot tip, changes within that block.
    Rollback : Slot → DeltaUTxOHistory
        -- ^ Rollback tip.
    Prune : SlotNo → DeltaUTxOHistory
        -- ^ Move finality forward.

{-# COMPILE AGDA2HS DeltaUTxOHistory #-}

-- | (Internal, exported for technical reasons.)
--
-- Roll forward under the assumption that we are moving to the future.
rollForwardBare
  : SlotNo → DeltaUTxO → UTxOHistory → UTxOHistory
rollForwardBare newTip delta old = record
    { history = UTxO.union history (DeltaUTxO.received delta)
    ; created =
        Timeline.insertMany
            (WithOrigin.At newTip) receivedTxIns created
    ; spent =
        Timeline.insertMany
            newTip excludedTxIns spent
    ; window = window
    ; boot = boot
    }
  where
    open UTxOHistory old

    receivedTxIns =
        Set.difference
            (dom (DeltaUTxO.received delta))
            (dom history)
    excludedTxIns =
        Set.difference
            (Set.intersection (DeltaUTxO.excluded delta) (dom history))
            (Map.keysSet (Timeline.getMapTime spent))

-- | (Internal, exported for technical reasons.)
rollForwardCases
  : SlotNo → DeltaUTxO → UTxOHistory → Maybe (RollbackWindow Slot) → UTxOHistory
rollForwardCases newTip delta old Nothing = old
rollForwardCases newTip delta old (Just window') =
    record new' { window = window' }
  where
    new' = rollForwardBare newTip delta old

{-|
Include the information contained in the block at 'SlotNo'
into the 'UTxOHistory'.
We expect that the block has already been digested into a single 'DeltaUTxO'.
-}
rollForward : SlotNo → DeltaUTxO → UTxOHistory → UTxOHistory
rollForward newTip delta old =
  rollForwardCases newTip delta old
    (RollbackWindow.rollForward (WithOrigin.At newTip) window)
  where
    open UTxOHistory old

{-# COMPILE AGDA2HS rollForwardCases #-}
{-# COMPILE AGDA2HS rollForwardBare #-}
{-# COMPILE AGDA2HS rollForward #-}

-- | (Internal, exported for technical reasons.)
rollBackwardBareSpent
  : Slot → Timeline.Timeline SlotNo TxIn → Timeline.Timeline SlotNo TxIn
rollBackwardBareSpent WithOrigin.Origin spents = Timeline.empty
rollBackwardBareSpent (WithOrigin.At slot) spents = Timeline.dropAfter slot spents

-- | (Internal, exported for technical reasons.)
--
-- Roll backwards under the assumption that we are moving to the past.
rollBackwardBare
  : Slot → UTxOHistory → UTxOHistory
rollBackwardBare newTip old = record
    { history = excluding history rolledCreated
    ; created = created'
    ; spent = rollBackwardBareSpent newTip spent
    ; window = window
    ; boot = boot
    }
  where
    open UTxOHistory old

    deletedAfter = Timeline.deleteAfter newTip created
    rolledCreated = fst deletedAfter
    created' = snd deletedAfter

-- | (Internal, exported for technical reasons.)
rollBackwardCases
  : Slot → UTxOHistory
  → RollbackWindow.MaybeRollback (RollbackWindow Slot) → UTxOHistory
rollBackwardCases newTip old RollbackWindow.Future = old
rollBackwardCases newTip old RollbackWindow.Past = empty (UTxOHistory.boot old)
rollBackwardCases newTip old (RollbackWindow.Present window') =
    record new' { window = window' }
  where
    new' = rollBackwardBare newTip old

{-|
Roll back the 'UTxOHistory' to the given 'Slot',
i.e. forget about all blocks that are strictly later than this slot.
-}
rollBackward : Slot → UTxOHistory → UTxOHistory
rollBackward newTip old =
  rollBackwardCases newTip old (RollbackWindow.rollBackward newTip window)
  where
    open UTxOHistory old

{-# COMPILE AGDA2HS rollBackwardBareSpent #-}
{-# COMPILE AGDA2HS rollBackwardBare #-}
{-# COMPILE AGDA2HS rollBackwardCases #-}
{-# COMPILE AGDA2HS rollBackward #-}

{-|
Remove the ability to 'rollback' before the given 'SlotNo',
but rolling back to genesis is always possible.

Using 'prune' will free up some space as old information
can be summarized and discarded.
-}
prune : SlotNo → UTxOHistory → UTxOHistory
prune newFinality old =
  case RollbackWindow.prune (WithOrigin.At newFinality) window of λ
    { Nothing → old
    ; (Just window') →
        let
            (prunedTxIns , spent') =
                Timeline.dropWhileAntitone (_<= newFinality) spent
        in
            record
                { history = excluding history prunedTxIns
                ; created = Timeline.difference created prunedTxIns
                ; spent = spent'
                ; window = window'
                ; boot = boot
                }
    }
  where
    open UTxOHistory old

{-# COMPILE AGDA2HS prune #-}

-- | How to apply a DeltaUTxOHistory to a UTxOHistory
applyDeltaUTxOHistory
    : DeltaUTxOHistory → UTxOHistory → UTxOHistory
applyDeltaUTxOHistory (AppendBlock newTip delta) =
    rollForward newTip delta
applyDeltaUTxOHistory (Rollback newTip) =
    rollBackward newTip
applyDeltaUTxOHistory (Prune newFinality) =
    prune newFinality

{-# COMPILE AGDA2HS applyDeltaUTxOHistory #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
--
lemma-<-<=
  : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → (x < y) ≡ not (y <= x)
--
lemma-<-<= x y
  rewrite  lte2gte y x
    | gte2GtEq x y
    | compareGt x y
    | compareEq x y
    | compareLt x y
  with compare x y
... | LT = refl
... | EQ = refl
... | GT = refl

-- | Rolling forward to the tip or before the tip does nothing.
@0 prop-rollForward-present
  : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot : SlotNo)
  → (WithOrigin.At slot <= getTip u) ≡ True
  → rollForward slot du u ≡ u
--
prop-rollForward-present u du newTip cond
  with (RollbackWindow.rollForward (WithOrigin.At newTip) (UTxOHistory.window u)) in eq
... | Nothing = refl
... | Just x = case lem1 of λ ()
  where
    roll = RollbackWindow.rollForward (WithOrigin.At newTip) (UTxOHistory.window u)
    lem1 =
      begin
        True
      ≡⟨ cong isJust (sym eq) ⟩
        isJust roll
      ≡⟨ RollbackWindow.prop-isJust-rollForward (WithOrigin.At newTip) (UTxOHistory.window u) ⟩
        (RollbackWindow.tip (UTxOHistory.window u) < WithOrigin.At newTip)
      ≡⟨ lemma-<-<= (getTip u) _ ⟩
        not (WithOrigin.At newTip <= getTip u)
      ≡⟨ cong not cond ⟩
        False
      ∎

-- | Rolling backward to the future does nothing.
prop-rollBackward-future
  : ∀ (u : UTxOHistory) (slot : Slot)
  → (getTip u <= slot) ≡ True
  → rollBackward slot u ≡ u
--
prop-rollBackward-future u newTip cond
  with RollbackWindow.rollBackward newTip (UTxOHistory.window u) in eq
... | RollbackWindow.Past =
    case (trans (sym eq) (RollbackWindow.prop-rollBackward-tip→Future newTip (UTxOHistory.window u) cond)) of λ ()
... | RollbackWindow.Present x =
    case (trans (sym eq) (RollbackWindow.prop-rollBackward-tip→Future newTip (UTxOHistory.window u) cond)) of λ ()
... | RollbackWindow.Future = refl

-- | Rolling backward to the tip does nothing, as we are already at the tip.
-- Special case of __prop-rollBackward-future__.
prop-rollBackward-tip
  : ∀ (u : UTxOHistory)
  → rollBackward (getTip u) u ≡ u
--
prop-rollBackward-tip u =
  prop-rollBackward-future u (getTip u) (reflexivity (getTip u))

postulate
 -- | Rolling forward updates the 'UTxO'.
 prop-rollForward-getUTxO
  : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot : SlotNo)
  → (getTip u < WithOrigin.At slot) ≡ True
  → getUTxO (rollForward slot du u)
    ≡ DeltaUTxO.apply du (getUTxO u)

{-----------------------------------------------------------------------------
    Properties
    Essentials
------------------------------------------------------------------------------}
--
lemma-equality-UTxOHistory
  : ∀ (u1 u2 : UTxOHistory)
  → UTxOHistory.history u1 ≡ UTxOHistory.history u2
  → UTxOHistory.created u1 ≡ UTxOHistory.created u2
  → UTxOHistory.spent u1 ≡ UTxOHistory.spent u2
  → UTxOHistory.window u1 ≡ UTxOHistory.window u2
  → UTxOHistory.boot u1 ≡ UTxOHistory.boot u2
  → u1 ≡ u2
--
lemma-equality-UTxOHistory u1 u2 refl refl refl refl refl = refl

--
lemma-WithOrigin-At-monotonic
  : ∀ (x y : SlotNo)
  → (WithOrigin.At x < WithOrigin.At y) ≡ (x < y)
--
lemma-WithOrigin-At-monotonic x y = refl

@0 lemma-UTxO-difference
  : ∀ (x y : UTxO)
  → (Set.difference (dom x) (dom y)) ⋪ (y ∪ x)
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

-- | Rolling backward will cancel rolling forward.
-- Bare version.
@0 lemma-rollBackward-rollForward-cancel
  : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot1 : Slot) (slot2 : SlotNo)
  → (slot1 < WithOrigin.At slot2) ≡ True
  → rollBackwardBare slot1 (rollForwardBare slot2 du u)
    ≡ rollBackwardBare slot1 u
--
lemma-rollBackward-rollForward-cancel u du slot1 slot2 cond =
    lemma-equality-UTxOHistory u1 u2
      lemHistory
      (Timeline.prop-dropAfter-insertMany slot1 (WithOrigin.At slot2) _ (UTxOHistory.created u) cond)
      lemSpent
      refl
      refl
  where
    u1 = rollBackwardBare slot1 (rollForwardBare slot2 du u)
    u2 = rollBackwardBare slot1 u

    txs1 = fst (Timeline.deleteAfter slot1 (UTxOHistory.created (rollForwardBare slot2 du u)))
    txs2 = fst (Timeline.deleteAfter slot1 (UTxOHistory.created u))
    receivedTxIns =
        Set.difference
            (dom (DeltaUTxO.received du))
            (dom (UTxOHistory.history u))

    lemTxs : txs1 ≡ Set.union txs2 receivedTxIns
    lemTxs = Timeline.prop-deleteAfter-insertMany slot1 (WithOrigin.At slot2) receivedTxIns (UTxOHistory.created u) cond

    lemReceivedTxIns
      : (receivedTxIns ⋪ (UTxOHistory.history u ∪ DeltaUTxO.received du))
        ≡ UTxOHistory.history u
    lemReceivedTxIns =
      lemma-UTxO-difference (DeltaUTxO.received du) (UTxOHistory.history u)

    lemHistory : UTxOHistory.history u1 ≡ UTxOHistory.history u2
    lemHistory =
      begin
        UTxOHistory.history u1
      ≡⟨⟩
        txs1 ⋪ (UTxOHistory.history u ∪ DeltaUTxO.received du)
      ≡⟨ cong (λ o → o ⋪ _) lemTxs ⟩
        (Set.union txs2 receivedTxIns) ⋪ (UTxOHistory.history u ∪ DeltaUTxO.received du)
      ≡⟨ sym (UTxO.prop-excluding-excluding {txs2} {receivedTxIns} {UTxOHistory.history u ∪ DeltaUTxO.received du}) ⟩
        (txs2 ⋪ (receivedTxIns ⋪ (UTxOHistory.history u ∪ DeltaUTxO.received du)))
      ≡⟨ cong (λ o → txs2 ⋪ o) lemReceivedTxIns ⟩
        (txs2 ⋪ UTxOHistory.history u)
      ≡⟨⟩
        UTxOHistory.history u2
      ∎

    lemSpent : UTxOHistory.spent u1 ≡ UTxOHistory.spent u2
    lemSpent = case slot1 of λ
      { WithOrigin.Origin {{eq}} →
        begin
          UTxOHistory.spent u1
        ≡⟨⟩
          rollBackwardBareSpent slot1 (UTxOHistory.spent (rollForwardBare slot2 du u))
        ≡⟨ cong (λ o → rollBackwardBareSpent o _) eq ⟩
          Timeline.empty
        ≡⟨ sym (cong (λ o → rollBackwardBareSpent o _) eq) ⟩
          UTxOHistory.spent u2
        ∎
      ; (WithOrigin.At slot) {{eq}} →
        begin
          UTxOHistory.spent u1
        ≡⟨⟩
          rollBackwardBareSpent slot1 (UTxOHistory.spent (rollForwardBare slot2 du u))
        ≡⟨ cong (λ o → rollBackwardBareSpent o _) eq ⟩
          Timeline.dropAfter slot (UTxOHistory.spent (rollForwardBare slot2 du u))
        ≡⟨ Timeline.prop-dropAfter-insertMany slot slot2 _ (UTxOHistory.spent u) (trans (sym (lemma-WithOrigin-At-monotonic slot slot2)) (subst (λ o → (o < WithOrigin.At slot2) ≡ True) eq cond)) ⟩
          Timeline.dropAfter slot (UTxOHistory.spent u)
        ≡⟨ sym (cong (λ o → rollBackwardBareSpent o _) eq) ⟩
          UTxOHistory.spent u2
        ∎
      }

--
lemma-rollBackwardBare-ignores-window
  : ∀ (slot : Slot) (u : UTxOHistory) (w : RollbackWindow Slot)
  → rollBackwardBare slot (record u {window = w})
    ≡ record (rollBackwardBare slot u) {window = w}
--
lemma-rollBackwardBare-ignores-window slot u w = refl

--
postulate
 lemma-rollback-window
  : ∀ (w w' : RollbackWindow Slot) (slot1 slot2 : Slot)
  → (slot1 < slot2) ≡ True
  → RollbackWindow.rollForward slot2 w ≡ Just w'
  → RollbackWindow.rollBackward slot1 w'
    ≡ RollbackWindow.rollBackward slot1 w
--

--
lemma-antisymmetry
  : ∀ {{_ : Ord a}} {{_ : IsLawfulOrd a}}
      {x y : a}
  → (x < y) ≡ True
  → (x >= y) ≡ True
  → ⊥
--
lemma-antisymmetry {a} {x} {y}
  rewrite compareLt x y
    | gte2GtEq x y
    | compareGt x y
    | compareEq x y
  with compare x y
... | LT = λ o ()
... | EQ = λ ()
... | GT = λ ()

--
@0 lemma-rollback-window-future
  : ∀ (w w' : RollbackWindow Slot) (slot1 slot2 : Slot)
  → (slot1 < slot2) ≡ True
  → RollbackWindow.rollForward slot2 w ≡ Just w'
  → RollbackWindow.rollBackward slot1 w' ≡ RollbackWindow.Future
  → ⊥
--
lemma-rollback-window-future w w' slot1 slot2 ord eq eq' =
    lemma-antisymmetry {Slot} {slot1} {slot2} ord lem4
  where
    lem1 : (RollbackWindow.tip w' <= slot1) ≡ True
    lem1 = RollbackWindow.prop-rollBackward-Future→tip slot1 w' eq'

    lem2 : RollbackWindow.tip w' ≡ slot2
    lem2 = RollbackWindow.prop-tip-rollForward slot2 w w' eq

    lem3 : (slot2 <= slot1) ≡ True
    lem3 = trans (cong (λ o → o <= slot1) (sym lem2)) lem1

    lem4 : (slot1 >= slot2) ≡ True
    lem4 = trans (sym (lte2gte slot2 slot1)) lem3

-- | /Essential property:/
-- Rolling backward will cancel rolling forward.
@0 prop-rollBackward-rollForward-cancel
  : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot1 : Slot) (slot2 : SlotNo)
  → (slot1 < WithOrigin.At slot2) ≡ True
  → rollBackward slot1 (rollForward slot2 du u)
    ≡ rollBackward slot1 u
--
prop-rollBackward-rollForward-cancel u du slot1 slot2 cond
  with RollbackWindow.rollForward (WithOrigin.At slot2) (UTxOHistory.window u) in eq2
... | Nothing = refl
... | Just window'
    rewrite lemma-rollback-window (UTxOHistory.window u) window' slot1 (WithOrigin.At slot2) cond eq2
    with RollbackWindow.rollBackward slot1 (UTxOHistory.window u) in eq1
...   | RollbackWindow.Future =
          magic (lemma-rollback-window-future (UTxOHistory.window u) window' slot1 (WithOrigin.At slot2) cond eq2 eq0)
        where
          eq0 =
            begin
              RollbackWindow.rollBackward slot1 window'
            ≡⟨ lemma-rollback-window (UTxOHistory.window u) window' slot1 (WithOrigin.At slot2) cond eq2 ⟩
              RollbackWindow.rollBackward slot1 (UTxOHistory.window u)
            ≡⟨ eq1 ⟩
              RollbackWindow.Future
            ∎
...   | RollbackWindow.Past = refl
...   | RollbackWindow.Present w =
      begin
        record (rollBackwardBare slot1 (record (rollForwardBare slot2 du u){window = window'})){window = w}
      ≡⟨ cong (λ o → record o {window = w}) (lemma-rollBackwardBare-ignores-window slot1 (rollForwardBare slot2 du u) window') ⟩
        record (rollBackwardBare slot1 (rollForwardBare slot2 du u)){window = w}
      ≡⟨ cong (λ o → record o {window = w}) (lemma-rollBackward-rollForward-cancel u du slot1 slot2 cond) ⟩
        record (rollBackwardBare slot1 u){window = w}
      ≡⟨⟩
        rollBackwardCases slot1 u (RollbackWindow.Present w)
      ∎

{-----------------------------------------------------------------------------
    Properties
    Consequences
------------------------------------------------------------------------------}
-- | Rolling backward after a 'rollForward' will restore the original state.
@0 prop-rollBackward-tip-rollForward
  : ∀ (u : UTxOHistory) (du : DeltaUTxO) (slot : SlotNo)
  → rollBackward (getTip u) (rollForward slot du u) ≡ u
--
prop-rollBackward-tip-rollForward u du slot =
  case (getTip u < WithOrigin.At slot) of λ
    { True {{eq}} →
      begin
        rollBackward (getTip u) (rollForward slot du u)
      ≡⟨ prop-rollBackward-rollForward-cancel u du (getTip u) slot eq ⟩
        rollBackward (getTip u) u
      ≡⟨ prop-rollBackward-tip u ⟩
        u
      ∎
    ; False {{eq}} →
      begin
        rollBackward (getTip u) (rollForward slot du u)
      ≡⟨ cong (λ o → rollBackward (getTip u) o) {rollForward slot du u} {u} (prop-rollForward-present u du slot (lem2 (getTip u) (WithOrigin.At slot) eq)) ⟩
        rollBackward (getTip u) u
      ≡⟨ prop-rollBackward-tip u ⟩
        u
      ∎
    }
 where
  lem2 : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
    → ∀ (x y : a) → (x < y) ≡ False → (y <= x) ≡ True
  lem2 x y h
    rewrite lte2ngt y x
    = cong not (trans (sym (lt2gt x y)) h)
