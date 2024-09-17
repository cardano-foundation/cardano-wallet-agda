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

-- | Returns the UTxO.
getUTxO : UTxOHistory → UTxO
getUTxO us =
    excluding history (Map.keysSet (Timeline.getMapTime spent))
  where
    open UTxOHistory us

-- | Returns the 'RollbackWindow' slot.
getRollbackWindow : UTxOHistory → RollbackWindow.RollbackWindow Slot
getRollbackWindow x = UTxOHistory.window x

-- | Returns the spent TxIns that can be rolled back.
getSpent : UTxOHistory → Map TxIn SlotNo
getSpent = Timeline.getMapTime ∘ UTxOHistory.spent

{-# COMPILE AGDA2HS getUTxO #-}
{-# COMPILE AGDA2HS getRollbackWindow #-}
{-# COMPILE AGDA2HS getSpent #-}

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
