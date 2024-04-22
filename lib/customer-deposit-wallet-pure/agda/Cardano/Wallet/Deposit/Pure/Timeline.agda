{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.Timeline
    {-
    ; Timeline
        ; atTime
        ; getTip
        ; rollForward
        ; rollBackward
        ; filterRange
        ; toAscList
    -}
    where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Read using
    ( Slot
    )

import Haskell.Data.Map as Map

variable
  time : Set

{-----------------------------------------------------------------------------
    Timeline
------------------------------------------------------------------------------}
-- | A 'Timeline' is a collection of events at certain
-- points in time (Slots).
record Timeline (time a : Set) {{_ : Ord time}} : Set where
  field
    events : Map.Map time a
    tip : time

open Timeline public

-- | Look up event at a particular time.
atTime : ∀ {{_ : Ord time}} → time → Timeline time a → Maybe a
atTime t = Map.lookup t ∘ events

-- | The tip of the timeline.
getTip : ∀ {{_ : Ord time}} → Timeline time a → time
getTip = tip

-- | Record the result of the next event in the timeline
rollForward
    : ∀ {{_ : Ord time}}
    → time → a → Timeline time a → Timeline time a
rollForward time a xs =
    if time > tip xs
    then record
        { events = Map.insert time a (events xs)
        ; tip = time
        }
    else xs

-- | Discard events later than the given 'Slot'.
rollBackward
    : ∀ {{_ : Ord time}}
    → time → Timeline time a → Timeline time a
rollBackward time xs =
    if time < tip xs
    then record
        { events = Map.takeWhileAntitone (_<= time) (events xs)
        ; tip = time
        }
    else xs

-- | Get all events within a range.
-- The range is exclusive in the low, but inclusive in the high.
filterRange
    : ∀ {{_ : Ord time}}
    → time × time → Timeline time a → Timeline time a
filterRange (low , high) xs = record
    { events =
        Map.takeWhileAntitone (_<= high)
            (Map.takeWhileAntitone (_> low) (events xs))
    ; tip = tip xs
    }

-- | Convert to an ascending list of events.
toAscList
    : ∀ {{_ : Ord time}}
    → Timeline time a → List (time × a)
toAscList = Map.toAscList ∘ events

{-# COMPILE AGDA2HS Timeline #-}
{-# COMPILE AGDA2HS atTime #-}
{-# COMPILE AGDA2HS getTip #-}
{-# COMPILE AGDA2HS rollForward #-}
{-# COMPILE AGDA2HS rollBackward #-}
{-# COMPILE AGDA2HS filterRange #-}
{-# COMPILE AGDA2HS toAscList #-}
