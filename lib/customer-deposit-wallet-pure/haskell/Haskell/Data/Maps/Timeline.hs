{-# LANGUAGE LambdaCase #-}
module Haskell.Data.Maps.Timeline where

import Data.Set (Set)
import Haskell.Data.List (foldl')
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map (empty, insert, lookup, restrictKeys, spanAntitone, toAscList, withoutKeys)
import qualified Haskell.Data.Maps.InverseMap as InverseMap (InverseMap, difference, insertManyKeys)
import Haskell.Data.Maybe (fromMaybe)
import qualified Haskell.Data.Set as Set (empty, toAscList)

insertManyKeys ::
                 (Ord key, Ord v) => Set key -> v -> Map key v -> Map key v
insertManyKeys keys v m0
  = foldl' (\ m key -> Map.insert key v m) m0 keys

data Timeline time a = Timeline{events :: Map a time,
                                eventsByTime :: InverseMap.InverseMap a time}

empty :: (Ord time, Ord a) => Timeline time a
empty = Timeline Map.empty Map.empty

lookupByTime ::
               (Ord time, Ord a) => time -> Timeline time a -> Set a
lookupByTime t
  = fromMaybe Set.empty . Map.lookup t . \ r -> eventsByTime r

lookupByItem ::
               (Ord time, Ord a) => a -> Timeline time a -> Maybe time
lookupByItem x = Map.lookup x . \ r -> events r

getMapTime :: (Ord time, Ord a) => Timeline time a -> Map a time
getMapTime = \ r -> events r

toAscList :: (Ord time, Ord a) => Timeline time a -> [(time, a)]
toAscList
  = concat .
      map
        (\case
             (t, xs) -> map (\ x -> (t, x)) (Set.toAscList xs))
        . Map.toAscList . \ r -> eventsByTime r

insertMany ::
             (Ord time, Ord a) =>
             time -> Set a -> Timeline time a -> Timeline time a
insertMany t xs timeline
  = Timeline (insertManyKeys xs t (events timeline))
      (InverseMap.insertManyKeys xs t (eventsByTime timeline))

difference ::
             (Ord time, Ord a) => Timeline time a -> Set a -> Timeline time a
difference timeline xs
  = Timeline (Map.withoutKeys (events timeline) xs)
      (InverseMap.difference (eventsByTime timeline)
         (Map.restrictKeys (events timeline) xs))

takeWhileAntitone ::
                    (Ord time, Ord a) =>
                    (time -> Bool) -> Timeline time a -> (Set a, Timeline time a)
takeWhileAntitone predicate timeline
  = (foldMap id
       (snd (Map.spanAntitone predicate (eventsByTime timeline))),
     Timeline
       (Map.withoutKeys (events timeline)
          (foldMap id
             (snd (Map.spanAntitone predicate (eventsByTime timeline)))))
       (fst (Map.spanAntitone predicate (eventsByTime timeline))))

dropWhileAntitone ::
                    (Ord time, Ord a) =>
                    (time -> Bool) -> Timeline time a -> (Set a, Timeline time a)
dropWhileAntitone predicate timeline
  = (foldMap id
       (fst (Map.spanAntitone predicate (eventsByTime timeline))),
     Timeline
       (Map.withoutKeys (events timeline)
          (foldMap id
             (fst (Map.spanAntitone predicate (eventsByTime timeline)))))
       (snd (Map.spanAntitone predicate (eventsByTime timeline))))

deleteAfter ::
              (Ord time, Ord a) =>
              time -> Timeline time a -> (Set a, Timeline time a)
deleteAfter t = takeWhileAntitone (<= t)

restrictRange ::
                (Ord time, Ord a) =>
                (time, time) -> Timeline time a -> Timeline time a
restrictRange (from, to)
  = \case
        (_, s) -> s
      .
      dropWhileAntitone (<= from) .
        \case
            (_, s) -> s
          . takeWhileAntitone (<= to)

