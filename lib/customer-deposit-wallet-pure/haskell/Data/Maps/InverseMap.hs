module Data.Maps.InverseMap where

import Data.Set (Set)
import Prelude hiding (null, subtract)

-- Working around a limitation in agda2hs.
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

type InverseMap key v = Map v (Set key)

empty :: (Ord key, Ord v) => InverseMap key v
empty = Map.empty

inverseMapFromMap
    :: (Ord key, Ord v) => Map key v -> InverseMap key v
inverseMapFromMap m =
    Map.fromListWith Set.union
        $ do
            (key, v) <- Map.toAscList m
            pure (v, Set.singleton key)

-- |
-- Insert a key-value pair into an 'InverseMap'.
insert
    :: (Ord key, Ord v)
    => key
    -> v
    -> InverseMap key v
    -> InverseMap key v
insert key v = Map.insertWith Set.union v (Set.singleton key)

-- |
-- Insert a set of keys that all have the same value.
insertManyKeys
    :: (Ord key, Ord v)
    => Set key
    -> v
    -> InverseMap key v
    -> InverseMap key v
insertManyKeys keys v =
    if Set.null keys then id else Map.insertWith Set.union v keys

deleteFromSet :: Ord v => v -> Set v -> Maybe (Set v)
deleteFromSet x vs =
    if Set.null (Set.delete x vs)
        then Nothing
        else Just (Set.delete x vs)

delete
    :: (Ord v, Ord key)
    => key
    -> v
    -> InverseMap key v
    -> InverseMap key v
delete key x = Map.update (deleteFromSet key) x

-- |
-- Take the difference between an 'InverseMap' and an ordinary 'Map'
difference
    :: (Ord v, Ord key)
    => InverseMap key v
    -> Map key v
    -> InverseMap key v
difference whole part =
    foldl' (\m keyx -> delete (fst keyx) (snd keyx) m) whole
        $ Map.toAscList part
