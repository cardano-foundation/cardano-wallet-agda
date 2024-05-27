module Haskell.Data.Maps.InverseMap where

import Data.Set (Set)
import Haskell.Data.List (foldl')
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map (empty, fromListWith, insertWith, toAscList, update)
import qualified Haskell.Data.Set as Set (delete, null, singleton, union)

type InverseMap key v = Map v (Set key)

empty :: (Ord key, Ord v) => InverseMap key v
empty = Map.empty

inverseMapFromMap ::
                    (Ord key, Ord v) => Map key v -> InverseMap key v
inverseMapFromMap m
  = Map.fromListWith Set.union $
      do (key, v) <- Map.toAscList m
         pure (v, Set.singleton key)

insert ::
         (Ord key, Ord v) =>
         key -> v -> InverseMap key v -> InverseMap key v
insert key v = Map.insertWith Set.union v (Set.singleton key)

insertManyKeys ::
                 (Ord key, Ord v) =>
                 Set key -> v -> InverseMap key v -> InverseMap key v
insertManyKeys keys v
  = if Set.null keys then id else Map.insertWith Set.union v keys

deleteFromSet :: Ord v => v -> Set v -> Maybe (Set v)
deleteFromSet x vs
  = if Set.null (Set.delete x vs) then Nothing else
      Just (Set.delete x vs)

delete ::
         (Ord v, Ord key) =>
         key -> v -> InverseMap key v -> InverseMap key v
delete key x = Map.update (deleteFromSet key) x

difference ::
             (Ord v, Ord key) =>
             InverseMap key v -> Map key v -> InverseMap key v
difference whole part
  = foldl' (\ m keyx -> delete (fst keyx) (snd keyx) m) whole $
      Map.toAscList part

