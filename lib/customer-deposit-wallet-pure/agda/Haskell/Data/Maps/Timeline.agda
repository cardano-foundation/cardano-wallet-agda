{-# OPTIONS --erasure #-}

module Haskell.Data.Maps.Timeline where

open import Haskell.Prelude hiding (fromMaybe)
open import Haskell.Reasoning

open import Haskell.Data.List using
    ( foldl'
    )
open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Maybe using
    ( fromMaybe
    )
open import Haskell.Data.Set using
    ( ℙ
    )

import Haskell.Data.Maps.InverseMap as InverseMap
import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

variable
  time : Set

{-----------------------------------------------------------------------------
    Helpers
------------------------------------------------------------------------------}

-- | Insert a set of keys into a 'Map' that all have the same value.
--
-- (Internal, exported for technical reasons.)
insertManyKeys
    : ∀ {key v : Set} {{_ : Ord key}} {{_ : Ord v}}
    → ℙ key → v → Map key v → Map key v
insertManyKeys keys v m0 =
    foldl' (\m key → Map.insert key v m) m0 keys

{-# COMPILE AGDA2HS insertManyKeys #-}

{-----------------------------------------------------------------------------
    Timeline
------------------------------------------------------------------------------}
-- | A 'Timeline' is a set of items that are associated with a timestamp.
-- Each item is unique.
-- Multiple items can have the same timestamp associated with it.
record Timeline (time a : Set) {{@0 _ : Ord time}} {{@0 _ : Ord a}} : Set where
  field
    events : Map a time
    eventsByTime : InverseMap.InverseMap a time

open Timeline public

-- | The empty set of items.
empty 
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → Timeline time a
empty = record { events = Map.empty; eventsByTime = Map.empty }

-- | Look up all items with a particular timestamp.
lookupByTime
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → time → Timeline time a → ℙ a
lookupByTime t = fromMaybe Set.empty ∘ Map.lookup t ∘ eventsByTime

-- | Look up the timestamp of a particular item.
lookupByItem
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → a → Timeline time a → Maybe time
lookupByItem x = Map.lookup x ∘ events

-- | Convert to a map (cheap).
getMapTime
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → Timeline time a → Map a time
getMapTime = events

-- | Set of items currently contained in the 'Timeline'.
items
  : ∀ {{_ : Ord time}} {{_ : Ord a}}
  → Timeline time a → ℙ a
items = Map.keysSet ∘ getMapTime

-- | Convert to a list of items, ascending by timestamp.
toAscList
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → Timeline time a → List (time × a)
toAscList =
    concat
    ∘ map (λ {(t , xs) → map (λ x → (t , x)) (Set.toAscList xs)})
    ∘ Map.toAscList
    ∘ eventsByTime

-- | Insert a single item.
insert
    : {{_ : Ord time}} {{_ : Ord a}}
    → time → a → Timeline time a → Timeline time a
insert t x timeline = record
    { events = Map.insert x t (events timeline)
    ; eventsByTime = InverseMap.insert x t (eventsByTime timeline)
    }

-- | Insert a set of items that all have the same timestamp.
insertMany
    : {{_ : Ord time}} {{_ : Ord a}}
    → time → ℙ a → Timeline time a → Timeline time a
insertMany t xs timeline = record
    { events = insertManyKeys xs t (events timeline)
    ; eventsByTime = InverseMap.insertManyKeys xs t (eventsByTime timeline)
    }

-- | Return the items that are not in the set.
difference
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → Timeline time a → ℙ a → Timeline time a
difference timeline xs = record
    { events = Map.withoutKeys (events timeline) xs
    ; eventsByTime =
        InverseMap.difference (eventsByTime timeline)
            (Map.restrictKeys (events timeline) xs)
    }

-- | Take while a predicate on the timestamps holds.
-- The predicate has to be antitonic.
--
-- This function also returns the set of items that were discarded.
takeWhileAntitone
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → (time → Bool) → Timeline time a → (ℙ a × Timeline time a)
takeWhileAntitone predicate timeline =
    let
        spanItems = Map.spanAntitone predicate (eventsByTime timeline)
        keptItems = fst spanItems
        deletedItems = foldMap id (snd spanItems)
    in  ( deletedItems
        , record
            { events = Map.withoutKeys (events timeline) deletedItems
            ; eventsByTime = keptItems
            }
        )

-- | Take while a predicate on the timestamps holds.
-- The predicate has to be antitonic.
--
-- This function also returns the set of items that were discarded.
dropWhileAntitone
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → (time → Bool) → Timeline time a → (ℙ a × Timeline time a)
dropWhileAntitone predicate timeline =
    let
        spanItems = Map.spanAntitone predicate (eventsByTime timeline)
        keptItems = snd spanItems
        deletedItems = foldMap id (fst spanItems)
    in  ( deletedItems
        , record
            { events = Map.withoutKeys (events timeline) deletedItems
            ; eventsByTime = keptItems
            }
        )

-- | Delete all items whose timestamp is after a given time.
--
-- This function also returns the set of items that were deleted.
deleteAfter
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → time → Timeline time a → (ℙ a × Timeline time a)
deleteAfter t = takeWhileAntitone (_<= t)

-- | Drop all items whose timestamp is after a given time.
--
-- > dropAfter t = snd ∘ deleteAfter t
dropAfter
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → time → Timeline time a → Timeline time a
dropAfter t = snd ∘ deleteAfter t

-- | Restrict the items to timestamps @from < time && time <= to@.
restrictRange
    : ∀ {{_ : Ord time}} {{_ : Ord a}}
    → (time × time) → Timeline time a → Timeline time a
restrictRange (from , to) =
    (λ {(_ , s) → s})
    ∘ dropWhileAntitone (_<= from)
    ∘ (λ {(_ , s) → s})
    ∘ takeWhileAntitone (_<= to)

{-# COMPILE AGDA2HS Timeline #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS lookupByTime #-}
{-# COMPILE AGDA2HS lookupByItem #-}
{-# COMPILE AGDA2HS getMapTime #-}
{-# COMPILE AGDA2HS items #-}
{-# COMPILE AGDA2HS toAscList #-}
{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS insertMany #-}
{-# COMPILE AGDA2HS difference #-}
{-# COMPILE AGDA2HS takeWhileAntitone #-}
{-# COMPILE AGDA2HS dropWhileAntitone #-}
{-# COMPILE AGDA2HS deleteAfter #-}
{-# COMPILE AGDA2HS dropAfter #-}
{-# COMPILE AGDA2HS restrictRange #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
postulate
 -- | 'insertMany' adds all items to the total set of items.
 prop-items-insertMany
  : ∀ {{_ : Ord time}} {{_ : Ord a}} {{_ : IsLawfulOrd time}}
      (t : time) (ys : ℙ a) (xs : Timeline time a)
  → items (insertMany t ys xs)
    ≡ Set.union ys (items xs)

 -- | 'dropAfter' cancels 'insertMany' from the future.
 prop-dropAfter-insertMany
  : ∀ {{_ : Ord time}} {{_ : Ord a}} {{_ : IsLawfulOrd time}}
      (t1 t2 : time) (ys : ℙ a) (xs : Timeline time a)
  → (t1 < t2) ≡ True
  → dropAfter t1 (insertMany t2 ys xs) ≡ dropAfter t1 xs

 -- | 'deleteAfter' deletes all items from the future.
 prop-deleteAfter-insertMany
  : ∀ {{_ : Ord time}} {{_ : Ord a}} {{_ : IsLawfulOrd time}}
      (t1 t2 : time) (ys : ℙ a) (xs : Timeline time a)
  → (t1 < t2) ≡ True
  → fst (deleteAfter t1 (insertMany t2 ys xs))
    ≡ Set.union (fst (deleteAfter t1 xs)) ys
