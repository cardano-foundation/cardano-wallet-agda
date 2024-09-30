-- | A type representing the inverse of a 'Map'
module Haskell.Data.Maps.InverseMap where

open import Haskell.Prelude

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

import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    Inverse Map
------------------------------------------------------------------------------}

variable
  key v : Set

InverseMap : ∀ (key v : Set) → {{@0 _ : Ord key}} → {{@0 _ : Ord v}} → Set
InverseMap key v = Map v (ℙ key)

{-# COMPILE AGDA2HS InverseMap #-}

empty
    : {{_ : Ord key}} → {{_ : Ord v}}
    → InverseMap key v
empty = Map.empty

{-# COMPILE AGDA2HS empty #-}

inverseMapFromMap
    : {{_ : Ord key}} → {{_ : Ord v}}
    → Map key v → InverseMap key v
inverseMapFromMap m = Map.fromListWith Set.union $ do
    (key , v) <- Map.toAscList m
    pure (v , Set.singleton key)

{-# COMPILE AGDA2HS inverseMapFromMap #-}

-- | Insert a key-value pair into an 'InverseMap'.
insert
    : {{_ : Ord key}} {{_ : Ord v}}
    → key → v → InverseMap key v → InverseMap key v
insert key v = Map.insertWith (Set.union) v (Set.singleton key)

{-# COMPILE AGDA2HS insert #-}

-- | Insert a set of keys that all have the same value.
insertManyKeys
    : {{_ : Ord key}} {{_ : Ord v}}
    → ℙ key → v → InverseMap key v → InverseMap key v
insertManyKeys keys v =
    if Set.null keys then id else Map.insertWith Set.union v keys

{-# COMPILE AGDA2HS insertManyKeys #-}

deleteFromSet
    : ∀ {v : Set} {{_ : Ord v}}
    → v → ℙ v → Maybe (ℙ v)
deleteFromSet x vs =
    let vs' = Set.delete x vs
    in  if Set.null vs' then Nothing else Just vs'

{-# COMPILE AGDA2HS deleteFromSet #-}

delete
    : {{_ : Ord v}} → {{_ : Ord key}}
    → key → v → InverseMap key v → InverseMap key v
delete key x = Map.update (deleteFromSet key) x

{-# COMPILE AGDA2HS delete #-}

-- | Take the difference between an 'InverseMap' and an ordinary 'Map'
difference
    : {{_ : Ord v}} → {{_ : Ord key}}
    → InverseMap key v → Map key v → InverseMap key v
difference whole part =
    foldl' (λ m keyx → delete (fst keyx) (snd keyx) m) whole
    $ Map.toAscList part

{-# COMPILE AGDA2HS difference #-}
