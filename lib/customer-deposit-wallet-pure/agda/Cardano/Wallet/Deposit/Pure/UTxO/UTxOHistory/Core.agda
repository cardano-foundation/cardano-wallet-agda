-- |
-- 'UTxOHistory' represents a history of a UTxO set that can be rolled
-- back (up to the 'finality' point).
module Cardano.Wallet.Deposit.Pure.UTxO.UTxOHistory.Core
    {-
      -- * Types
      UTxOHistory
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
open import Haskell.Data.Maybe using
    ( fromMaybe
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Set using
    ( ℙ
    )

import Cardano.Wallet.Deposit.Pure.RollbackWindow as RollbackWindow
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

-- | (Internal, exported for technical reasons.)
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
        ; window = RollbackWindow.singleton WithOrigin.Origin
        ; boot = utxo
        }

{-# COMPILE AGDA2HS empty #-}

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

-- | The spent 'TxIn's that can be rolled back.
--
-- (Internal, exported for specification.)
getSpent : UTxOHistory → Map TxIn SlotNo
getSpent = Timeline.getMapTime ∘ UTxOHistory.spent

{-# COMPILE AGDA2HS getUTxO #-}
{-# COMPILE AGDA2HS getRollbackWindow #-}
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

{-|
Include the information contained in the block at 'SlotNo'
into the 'UTxOHistory'.
We expect that the block has already been digested into a single 'DeltaUTxO'.
-}
appendBlock : SlotNo → DeltaUTxO → UTxOHistory → UTxOHistory
appendBlock newTip delta old =
  case RollbackWindow.rollForward (WithOrigin.At newTip) window of λ
    { Nothing → old
    ; (Just window') →
      record
        { history = UTxO.union history (DeltaUTxO.received delta)
        ; created =
            Timeline.insertMany
                (WithOrigin.At newTip) receivedTxIns created
        ; spent =
            Timeline.insertMany
                newTip excludedTxIns spent
        ; window = window'
        ; boot = boot
        }
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

{-# COMPILE AGDA2HS appendBlock #-}

{-|
Roll back the 'UTxOHistory' to the given 'Slot',
i.e. forget about all blocks that are strictly later than this slot.
-}
rollback : Slot → UTxOHistory → UTxOHistory
rollback newTip old =
  case RollbackWindow.rollBackward newTip window of λ
    { RollbackWindow.Future → old
    ; RollbackWindow.Past → empty boot
    ; (RollbackWindow.Present window') →
        let
            newTip' = RollbackWindow.tip window'
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
                ; window = window'
                ; boot = boot
                }
    }
  where
    open UTxOHistory old

{-# COMPILE AGDA2HS rollback #-}

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
    appendBlock newTip delta
applyDeltaUTxOHistory (Rollback newTip) =
    rollback newTip
applyDeltaUTxOHistory (Prune newFinality) =
    prune newFinality
