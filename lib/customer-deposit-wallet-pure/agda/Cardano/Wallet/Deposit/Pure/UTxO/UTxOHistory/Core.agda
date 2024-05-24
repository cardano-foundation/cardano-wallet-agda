-- |
-- 'UTxOHistory' represents a history of a UTxO set that can be rolled
-- back (up to the 'finality' point).
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core
    {-
      -- * Types
      UTxOHistory
    , Pruned (..)
    , Spent (..)

      -- * Observations
    , getTip
    , getFinality
    , empty
    , getUTxO

      -- * Changes
    , DeltaUTxOHistory (..)

      -- * For testing
    , getSpent

      -- * Store helpers
    , constrainingPrune
    , constrainingRollback
    , constrainingAppendBlock
    , reverseMapOfSets
    -}
    where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO using
    ( DeltaUTxO
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    ; dom
    ; excluding
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Type using
    ( Pruned
    ; UTxOHistory
    )
open import Cardano.Wallet.Deposit.Read using
    ( Slot
    ; SlotNo
    ; TxIn
    ; WithOrigin
    )
open import Haskell.Data.List using
    ( foldl'
    )
open import Haskell.Data.Maybe using
    ( fromMaybe
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Set using
    ( ℙ
    )

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

guard : Bool → Maybe ⊤
guard True = Just tt
guard False = Nothing

{-# COMPILE AGDA2HS guard #-}

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
        ; tip = WithOrigin.Origin
        ; finality = Pruned.NotPruned
        ; boot = utxo
        }

{-# COMPILE AGDA2HS empty #-}

-- | Returns the UTxO.
getUTxO : UTxOHistory → UTxO
getUTxO us =
    excluding history (Map.keysSet (Timeline.getMapTime spent))
  where
    open UTxOHistory us

-- | Returns the tip slot.
getTip : UTxOHistory → Slot
getTip = UTxOHistory.tip

-- | Returns the finality slot.
getFinality : UTxOHistory → Pruned
getFinality = UTxOHistory.finality

-- | Returns the spent TxIns that can be rolled back.
getSpent : UTxOHistory → Map TxIn SlotNo
getSpent = Timeline.getMapTime ∘ UTxOHistory.spent

{-# COMPILE AGDA2HS getUTxO #-}
{-# COMPILE AGDA2HS getTip #-}
{-# COMPILE AGDA2HS getFinality #-}
{-# COMPILE AGDA2HS getSpent #-}

{-----------------------------------------------------------------------------
    Helper functions
------------------------------------------------------------------------------}

-- | Helper to constraint the slot of an AppendBlock.
constrainingAppendBlock : a → UTxOHistory → SlotNo → a → a
constrainingAppendBlock noop us newTip f =
    if WithOrigin.At newTip <= UTxOHistory.tip us
    then noop
    else f

{-# COMPILE AGDA2HS constrainingAppendBlock #-}

-- | Helper to constrain the slot of a Rollback.
constrainingRollback : a → UTxOHistory → Slot → (Maybe Slot → a) → a
constrainingRollback noop us newTip f =
    if newTip >= tip
    then noop
    else f (case finality of λ
        { Pruned.NotPruned → Just newTip
        ; (Pruned.PrunedUpTo finality') → 
            if newTip >= WithOrigin.At finality'
                then Just newTip
                else Nothing
        })
  where
    open UTxOHistory us

{-# COMPILE AGDA2HS constrainingRollback #-}

-- | Helper to constraint the slot of a Prune.
constrainingPrune : a → UTxOHistory → SlotNo → (SlotNo → a) → a
constrainingPrune noop us newFinality f =
    fromMaybe noop $ do
        case finality of λ
            { Pruned.NotPruned → pure tt
            ; (Pruned.PrunedUpTo finality') → guard $ newFinality > finality'
            }
        case tip of λ
            { WithOrigin.Origin → Nothing
            ; (WithOrigin.At tip') → pure $ f $ min newFinality tip'
            }
  where
    open UTxOHistory us

{-# COMPILE AGDA2HS constrainingPrune #-}

{-----------------------------------------------------------------------------
    DeltaUTxOHistory
------------------------------------------------------------------------------}

-- | Changes to the UTxO history.
data DeltaUTxOHistory : Set where
    AppendBlock : SlotNo → DeltaUTxO → DeltaUTxOHistory
        -- ^ New slot tip, changes within that block.
    Rollback : Slot → DeltaUTxOHistory
        -- ^ Rollback tip.
    Prune : SlotNo → DeltaUTxOHistory
        -- ^ Move finality forward.

{-# COMPILE AGDA2HS DeltaUTxOHistory #-}

appendBlock : SlotNo → DeltaUTxO → UTxOHistory → UTxOHistory
appendBlock newTip delta noop =
    constrainingAppendBlock noop noop newTip
      record
        { history = UTxO.union history (DeltaUTxO.received delta)
        ; created =
            Timeline.insertMany
                (WithOrigin.At newTip) receivedTxIns created
        ; spent =
            Timeline.insertMany
                newTip excludedTxIns spent
        ; tip = WithOrigin.At newTip
        ; finality = finality
        ; boot = boot
        }
  where
    open UTxOHistory noop
    receivedTxIns =
        Set.difference
            (dom (DeltaUTxO.received delta))
            (dom history)
    excludedTxIns =
        Set.difference
            (Set.intersection (DeltaUTxO.excluded delta) (dom history))
            (Map.keysSet (Timeline.getMapTime spent))

{-# COMPILE AGDA2HS appendBlock #-}

rollback : Slot → UTxOHistory → UTxOHistory
rollback newTip noop =
  constrainingRollback noop noop newTip λ
    { (Just newTip') →
        let
            (rolledCreated , created') =
                Timeline.deleteAfter newTip' created
        in
            record
                { history = excluding history rolledCreated
                ; created = created'
                ; spent = case newTip' of λ
                    { WithOrigin.Origin → Timeline.empty
                    ; (WithOrigin.At slot'') →
                        snd (Timeline.takeWhileAntitone (_<= slot'') spent)
                    }
                ; tip = newTip'
                ; finality = finality
                ; boot = boot
                }
    ; Nothing → empty boot
    }
  where
    open UTxOHistory noop

{-# COMPILE AGDA2HS rollback #-}

prune : SlotNo → UTxOHistory → UTxOHistory
prune newFinality noop =
  constrainingPrune noop noop newFinality $ \newFinality' →
    let
        (prunedTxIns , spent') =
            Timeline.dropWhileAntitone (_<= newFinality') spent
    in
        record
            { history = excluding history prunedTxIns
            ; created = Timeline.difference created prunedTxIns
            ; spent = spent'
            ; tip = tip
            ; finality = Pruned.PrunedUpTo newFinality'
            ; boot = boot
            }
  where
    open UTxOHistory noop

{-# COMPILE AGDA2HS prune #-}

-- | How to apply a DeltaUTxOHistory to a UTxOHistory
applyDeltaUTxOHistory
    : DeltaUTxOHistory → UTxOHistory → UTxOHistory
applyDeltaUTxOHistory (AppendBlock newTip delta) =
    appendBlock newTip delta
applyDeltaUTxOHistory (Rollback newTip) =
    rollback newTip
applyDeltaUTxOHistory (Prune newFinality) =
    prune newFinality
