{-# OPTIONS --erasure #-}

module Data.Maps.Timeline
    {-|
      -- * Type
    ; Timeline

      -- * Construction
    ; empty

      -- * Observation
    ; lookupByTime
    ; lookupByItem
      ; prop-lookupByItem

    ; getMapTime
    ; items
        ; prop-items-empty

    ; toAscList

      -- * Operations
    ; insert
    ; insertMany
      ; prop-items-insertMany
    ; difference
    ; restrictRange
    ; takeWhileAntitone
    ; dropWhileAntitone
    ; deleteAfter
    ; dropAfter
      ; prop-dropAfter-deleteAfter

      -- * Internal
    ; insertManyKeys
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.List using
    ( foldl'
    )
open import Data.Map using
    ( Map
    )
open import Haskell.Data.Maybe using
    ( fromMaybe
    ; isJust
    )
open import Data.Set using
    ( ℙ
    )

import Data.Maps.InverseMap as InverseMap
import Data.Map as Map
import Data.Set as Set

{-# FOREIGN AGDA2HS
{-# LANGUAGE StrictData #-}
#-}

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
#-}

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

postulate
 prop-lookup-insertManyKeys
  : ∀ {k v : Set} {{_ : Ord k}} {{_ : Ord v}}
  → ∀ (key : k) (keys : ℙ k) (x : v) (m : Map k v)
  → Map.lookup key (insertManyKeys keys x m)
    ≡ (if elem key keys then Just x else Map.lookup key m)

{-----------------------------------------------------------------------------
    Timeline
------------------------------------------------------------------------------}
-- | A 'Timeline' is a set of items that are associated with a timestamp.
--
-- Each item is unique.
-- Multiple items can have the same timestamp associated with it.
record Timeline (time a : Set) {{@0 _ : Ord time}} {{@0 _ : Ord a}} : Set where
  field
    events : Map a time
    eventsByTime : InverseMap.InverseMap a time

open Timeline public

postulate instance
  iShowTimeline
    : ∀ {{@0 _ : Ord time}} {{@0 _ : Ord a}}
        {{_ : Show a}} {{_ : Show time}}
    → Show (Timeline time a)

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
{-# COMPILE AGDA2HS iShowTimeline derive #-}
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
    Basic
------------------------------------------------------------------------------}
-- | Definition of 'lookupByItem'.
prop-lookupByItem
  : ∀ {{_ : Ord time}} {{_ : Ord a}}
  → ∀ (x : a) (xs : Timeline time a)
  → lookupByItem x xs ≡ Map.lookup x (getMapTime xs)
--
prop-lookupByItem xs x = refl

-- | Definition of 'dropAfter' in terms of 'deleteAfter'.
prop-dropAfter-deleteAfter
  : ∀ {{_ : Ord time}} {{_ : Ord a}}
  → ∀ (t : time) (xs : Timeline time a)
  → dropAfter t xs ≡ snd (deleteAfter t xs)
--
prop-dropAfter-deleteAfter t xs = refl

-- | The 'empty' 'Timeline' does not contain any items.
prop-items-empty
  : ∀ {{_ : Ord time}} {{_ : Ord a}}
  → items {time} empty ≡ Set.empty {a}
--
prop-items-empty = Map.prop-keysSet-empty

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- | 'insertMany' adds all items to the total set of items.
prop-items-insertMany
  : ∀ {time a} {{_ : Ord time}} {{iOrda : Ord a}} {{_ : IsLawfulOrd time}}
  → ∀ (t : time) (ys : ℙ a) (xs : Timeline time a)
  → items (insertMany t ys xs)
    ≡ Set.union ys (items xs)
--
prop-items-insertMany {time} {a} {{_}} {{iOrda}} t ys xs =
    Set.prop-equality eq-member
  where
    eq-member
      : ∀ (z : a)
      → Set.member z (items (insertMany t ys xs))
        ≡ Set.member z (Set.union ys (items xs))
    eq-member z
      rewrite Map.prop-member-keysSet {{iOrda}} {z} {getMapTime (insertMany t ys xs)}
      rewrite prop-lookup-insertManyKeys z ys t (getMapTime xs)
      rewrite prop-if-apply (elem z ys) (Just t) (Map.lookup z (getMapTime xs)) isJust 
      rewrite sym (Map.prop-member-keysSet {{iOrda}} {z} {getMapTime xs})
      rewrite Set.prop-member-union z ys (items xs)
      rewrite Set.prop-member-toAscList z ys
      with Set.member z ys
      with Set.member z (items xs)
    ... | True  | True  = refl
    ... | False | True  = refl
    ... | True  | False = refl
    ... | False | False = refl

postulate
 -- | 'deleteAfter' returns the 'items' that were deleted.
 prop-fst-snd-deleteAfter
  : ∀ {{_ : Ord time}} {{_ : Ord a}} {{_ : IsLawfulOrd time}}
      (t : time) (xs : Timeline time a)
  → let (deleted , ys) = deleteAfter t xs 
    in  Set.union deleted (items ys) ≡ items xs

postulate
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
