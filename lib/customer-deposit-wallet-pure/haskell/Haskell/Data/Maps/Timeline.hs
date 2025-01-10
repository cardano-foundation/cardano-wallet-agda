{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData #-}

module Haskell.Data.Maps.Timeline
    ( -- * Type
      Timeline

      -- * Construction
    , empty

      -- * Observation
    , lookupByTime
    , lookupByItem
      -- $prop-lookupByItem
    , getMapTime
    , items
      -- $prop-items-empty
    , toAscList

      -- * Operations
    , insert
    , insertMany
    , difference
    , restrictRange
    , takeWhileAntitone
    , dropWhileAntitone
    , deleteAfter
    , dropAfter
      -- $prop-dropAfter-deleteAfter

      -- * Internal
    , insertManyKeys
    )
where

import Data.Set (Set)
import Haskell.Data.List (foldl')
import Haskell.Data.Map.Def (Map)
import qualified Haskell.Data.Map.Def as Map
    ( empty
    , insert
    , keysSet
    , lookup
    , restrictKeys
    , spanAntitone
    , toAscList
    , withoutKeys
    )
import qualified Haskell.Data.Maps.InverseMap as InverseMap
    ( InverseMap
    , difference
    , insert
    , insertManyKeys
    )
import Haskell.Data.Maybe (fromMaybe)
import qualified Haskell.Data.Set as Set (empty, toAscList)
import Prelude hiding (null, subtract)

-- |
-- Insert a set of keys into a 'Map' that all have the same value.
--
-- (Internal, exported for technical reasons.)
insertManyKeys
    :: (Ord key, Ord v) => Set key -> v -> Map key v -> Map key v
insertManyKeys keys v m0 =
    foldl' (\m key -> Map.insert key v m) m0 keys

-- |
-- A 'Timeline' is a set of items that are associated with a timestamp.
--
-- Each item is unique.
-- Multiple items can have the same timestamp associated with it.
data Timeline time a = Timeline
    { events :: Map a time
    , eventsByTime :: InverseMap.InverseMap a time
    }

deriving instance (Show a, Show time) => Show (Timeline time a)

-- |
-- The empty set of items.
empty :: (Ord time, Ord a) => Timeline time a
empty = Timeline Map.empty Map.empty

-- |
-- Look up all items with a particular timestamp.
lookupByTime
    :: (Ord time, Ord a) => time -> Timeline time a -> Set a
lookupByTime t =
    fromMaybe Set.empty . Map.lookup t . \r -> eventsByTime r

-- |
-- Look up the timestamp of a particular item.
lookupByItem
    :: (Ord time, Ord a) => a -> Timeline time a -> Maybe time
lookupByItem x = Map.lookup x . \r -> events r

-- |
-- Convert to a map (cheap).
getMapTime :: (Ord time, Ord a) => Timeline time a -> Map a time
getMapTime = \r -> events r

-- |
-- Set of items currently contained in the 'Timeline'.
items :: (Ord time, Ord a) => Timeline time a -> Set a
items = Map.keysSet . getMapTime

-- |
-- Convert to a list of items, ascending by timestamp.
toAscList :: (Ord time, Ord a) => Timeline time a -> [(time, a)]
toAscList =
    concat
        . map
            ( \case
                (t, xs) -> map (\x -> (t, x)) (Set.toAscList xs)
            )
        . Map.toAscList
        . \r -> eventsByTime r

-- |
-- Insert a single item.
insert
    :: (Ord time, Ord a)
    => time
    -> a
    -> Timeline time a
    -> Timeline time a
insert t x timeline =
    Timeline
        (Map.insert x t (events timeline))
        (InverseMap.insert x t (eventsByTime timeline))

-- |
-- Insert a set of items that all have the same timestamp.
insertMany
    :: (Ord time, Ord a)
    => time
    -> Set a
    -> Timeline time a
    -> Timeline time a
insertMany t xs timeline =
    Timeline
        (insertManyKeys xs t (events timeline))
        (InverseMap.insertManyKeys xs t (eventsByTime timeline))

-- |
-- Return the items that are not in the set.
difference
    :: (Ord time, Ord a) => Timeline time a -> Set a -> Timeline time a
difference timeline xs =
    Timeline
        (Map.withoutKeys (events timeline) xs)
        ( InverseMap.difference
            (eventsByTime timeline)
            (Map.restrictKeys (events timeline) xs)
        )

-- |
-- Take while a predicate on the timestamps holds.
-- The predicate has to be antitonic.
--
-- This function also returns the set of items that were discarded.
takeWhileAntitone
    :: (Ord time, Ord a)
    => (time -> Bool)
    -> Timeline time a
    -> (Set a, Timeline time a)
takeWhileAntitone predicate timeline =
    ( foldMap
        id
        (snd (Map.spanAntitone predicate (eventsByTime timeline)))
    , Timeline
        ( Map.withoutKeys
            (events timeline)
            ( foldMap
                id
                (snd (Map.spanAntitone predicate (eventsByTime timeline)))
            )
        )
        (fst (Map.spanAntitone predicate (eventsByTime timeline)))
    )

-- |
-- Take while a predicate on the timestamps holds.
-- The predicate has to be antitonic.
--
-- This function also returns the set of items that were discarded.
dropWhileAntitone
    :: (Ord time, Ord a)
    => (time -> Bool)
    -> Timeline time a
    -> (Set a, Timeline time a)
dropWhileAntitone predicate timeline =
    ( foldMap
        id
        (fst (Map.spanAntitone predicate (eventsByTime timeline)))
    , Timeline
        ( Map.withoutKeys
            (events timeline)
            ( foldMap
                id
                (fst (Map.spanAntitone predicate (eventsByTime timeline)))
            )
        )
        (snd (Map.spanAntitone predicate (eventsByTime timeline)))
    )

-- |
-- Delete all items whose timestamp is after a given time.
--
-- This function also returns the set of items that were deleted.
deleteAfter
    :: (Ord time, Ord a)
    => time
    -> Timeline time a
    -> (Set a, Timeline time a)
deleteAfter t = takeWhileAntitone (<= t)

-- |
-- Drop all items whose timestamp is after a given time.
dropAfter
    :: (Ord time, Ord a) => time -> Timeline time a -> Timeline time a
dropAfter t = (\r -> snd r) . deleteAfter t

-- |
-- Restrict the items to timestamps @from < time && time <= to@.
restrictRange
    :: (Ord time, Ord a)
    => (time, time)
    -> Timeline time a
    -> Timeline time a
restrictRange (from, to) =
    \case
        (_, s) -> s
        . dropWhileAntitone (<= from)
        . \case
            (_, s) -> s
        . takeWhileAntitone (<= to)

-- * Properties

-- $prop-dropAfter-deleteAfter
-- #p:prop-dropAfter-deleteAfter#
--
-- [prop-dropAfter-deleteAfter]:
--     Definition of 'dropAfter' in terms of 'deleteAfter'.
--
--     > prop-dropAfter-deleteAfter
--     >   : ∀ {{_ : Ord time}} {{_ : Ord a}}
--     >   → ∀ (t : time) (xs : Timeline time a)
--     >   → dropAfter t xs ≡ snd (deleteAfter t xs)

-- $prop-items-empty
-- #p:prop-items-empty#
--
-- [prop-items-empty]:
--     The 'empty' 'Timeline' does not contain any items.
--
--     > prop-items-empty
--     >   : ∀ {{_ : Ord time}} {{_ : Ord a}}
--     >   → items {time} empty ≡ Set.empty {a}

-- $prop-lookupByItem
-- #p:prop-lookupByItem#
--
-- [prop-lookupByItem]:
--     Definition of 'lookupByItem'.
--
--     > prop-lookupByItem
--     >   : ∀ {{_ : Ord time}} {{_ : Ord a}}
--     >   → ∀ (x : a) (xs : Timeline time a)
--     >   → lookupByItem x xs ≡ Map.lookup x (getMapTime xs)
