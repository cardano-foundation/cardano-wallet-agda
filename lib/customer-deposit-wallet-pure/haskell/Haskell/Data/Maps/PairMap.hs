{-# LANGUAGE ScopedTypeVariables #-}

module Haskell.Data.Maps.PairMap where

import Data.Set (Set)
import Haskell.Data.List (foldl')
import Haskell.Data.Map (Map)
import qualified Haskell.Data.Map as Map
    ( delete
    , empty
    , insert
    , keys
    , lookup
    , null
    , update
    )
import Haskell.Data.Maybe (fromMaybe)

explicitEmpty :: Ord a => Map a v -> Maybe (Map a v)
explicitEmpty m = if Map.null m then Nothing else Just m

implicitEmpty :: Ord a => Maybe (Map a v) -> Map a v
implicitEmpty = fromMaybe Map.empty

withEmpty
    :: Ord a => (Map a v -> Map a v) -> Maybe (Map a v) -> Maybe (Map a v)
withEmpty f = explicitEmpty . f . implicitEmpty

lookup2 :: (Ord a, Ord b) => a -> b -> Map a (Map b v) -> Maybe v
lookup2 a b m = Map.lookup a m >>= Map.lookup b

insert2
    :: (Ord a, Ord b) => a -> b -> v -> Map a (Map b v) -> Map a (Map b v)
insert2 ai bi v m =
    Map.insert
        ai
        (Map.insert bi v (implicitEmpty (Map.lookup ai m)))
        m

delete2
    :: (Ord a, Ord b) => a -> b -> Map a (Map b v) -> Map a (Map b v)
delete2 a b = Map.update (explicitEmpty . Map.delete b) a

delete2s
    :: (Ord a, Ord b) => [a] -> b -> Map a (Map b v) -> Map a (Map b v)
delete2s xs b m0 = foldr (\a -> delete2 a b) m0 xs

-- |
-- The type `PairMap a b v` is essentially the type `Map (a × b) v`,
-- but with two efficient lookup functions
--
-- > lookupA : a → PairMap a b v → Map b v
-- > lookupB : b → PairMap a b v → Map a v
--
-- The property `prop-lookupA-lookupB` states that these lookups
-- yield the same values.
--
-- In the terminology of relational database,
-- this type stores rows of the form `a × b × v`
-- and maintains an index on both the first column `a` and the second column `b`.
data PairMap a b v = PairMap
    { mab :: Map a (Map b v)
    , mba :: Map b (Map a v)
    }

empty :: forall a b v. (Ord a, Ord b) => PairMap a b v
empty = PairMap Map.empty Map.empty

lookupA
    :: forall a b v. (Ord a, Ord b) => a -> PairMap a b v -> Map b v
lookupA a = implicitEmpty . Map.lookup a . \r -> mab r

lookupB
    :: forall a b v. (Ord a, Ord b) => b -> PairMap a b v -> Map a v
lookupB b = implicitEmpty . Map.lookup b . \r -> mba r

lookupAB
    :: forall a b v. (Ord a, Ord b) => a -> b -> PairMap a b v -> Maybe v
lookupAB a b m = Map.lookup a (mab m) >>= Map.lookup b

insert
    :: forall a b v
     . (Ord a, Ord b)
    => a
    -> b
    -> v
    -> PairMap a b v
    -> PairMap a b v
insert ai bi v m =
    PairMap (insert2 ai bi v (mab m)) (insert2 bi ai v (mba m))

deleteA
    :: forall a b v
     . (Ord a, Ord b)
    => a
    -> PairMap a b v
    -> PairMap a b v
deleteA ai m =
    PairMap (Map.delete ai (mab m)) (delete2s bs ai (mba m))
  where
    bs :: [b]
    bs = Map.keys (implicitEmpty (Map.lookup ai (mab m)))

withoutKeysA
    :: forall a b v
     . (Ord a, Ord b)
    => PairMap a b v
    -> Set a
    -> PairMap a b v
withoutKeysA m0 xs = foldl' (\m x -> deleteA x m) m0 xs
