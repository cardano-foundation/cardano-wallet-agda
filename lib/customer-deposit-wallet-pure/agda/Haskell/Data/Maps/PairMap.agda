-- | A map from pairs of keys to values,
-- with efficient lookups for single keys.
module Haskell.Data.Maps.PairMap where

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

import Haskell.Data.Map as Map

variable
  v : Set

{-----------------------------------------------------------------------------
    Helper functions
------------------------------------------------------------------------------}

explicitEmpty : {{_ : Ord a}} → Map a v → Maybe (Map a v)
explicitEmpty m = if Map.null m then Nothing else Just m

implicitEmpty : {{_ : Ord a}} → Maybe (Map a v) → Map a v
implicitEmpty Nothing = Map.empty
implicitEmpty (Just x) = x 

withEmpty
  : {{_ : Ord a}}
  → (Map a v → Map a v)
  → Maybe (Map a v) → Maybe (Map a v)
withEmpty f = explicitEmpty ∘ f ∘ implicitEmpty

{-# COMPILE AGDA2HS explicitEmpty #-}
{-# COMPILE AGDA2HS implicitEmpty #-}
{-# COMPILE AGDA2HS withEmpty #-}

{-----------------------------------------------------------------------------
    Map a (Map b v)
    Helper functions and properties
------------------------------------------------------------------------------}

lookup2
  : {{_ : Ord a}} → {{_ : Ord b}} 
  → a → b → Map a (Map b v) → Maybe v
lookup2 a b m = Map.lookup a m >>= Map.lookup b

insert2
  : {{_ : Ord a}} → {{_ : Ord b}} 
  → a → b → v → Map a (Map b v) → Map a (Map b v)
insert2 ai bi v m =
  Map.insert ai (Map.insert bi v (implicitEmpty (Map.lookup ai m))) m

delete2
  : {{_ : Ord a}} → {{_ : Ord b}} 
  → a → b → Map a (Map b v) → Map a (Map b v)
delete2 a b = Map.update (explicitEmpty ∘ Map.delete b) a

delete2s
  : {{_ : Ord a}} → {{_ : Ord b}} 
  → List a → b → Map a (Map b v) → Map a (Map b v)
delete2s xs b m0 = foldr (λ a m → delete2 a b m) m0 xs
-- fixme: use foldl'

{-# COMPILE AGDA2HS lookup2 #-}
{-# COMPILE AGDA2HS insert2 #-}
{-# COMPILE AGDA2HS delete2 #-}
{-# COMPILE AGDA2HS delete2s #-}

{-----------------------------------------------------------------------------
    PairMap
------------------------------------------------------------------------------}

record PairMap (a b v : Set) {{orda : Ord a}} {{ordb : Ord b}} : Set where
  field
    mab : Map a (Map b v)
    mba : Map b (Map a v)

open PairMap public

module _ {a b v : Set} {{_ : Ord a}} {{_ : Ord b}} where
  empty : PairMap a b v
  empty = record { mab = Map.empty ; mba = Map.empty }

  lookupA : a → PairMap a b v → Map b v
  lookupA a = fromMaybe Map.empty ∘ Map.lookup a ∘ mab

  lookupB : b → PairMap a b v → Map a v
  lookupB b = fromMaybe Map.empty ∘ Map.lookup b ∘ mba

  lookupAB : a → b → PairMap a b v → Maybe v
  lookupAB a b m = Map.lookup a (mab m) >>= Map.lookup b

  insert : a → b → v → PairMap a b v → PairMap a b v
  insert ai bi v m = record
    { mab = insert2 ai bi v (mab m)
    ; mba = insert2 bi ai v (mba m)
    }

  deleteA : a → PairMap a b v → PairMap a b v
  deleteA ai m = record
      { mab = Map.delete ai (mab m)
      ; mba = delete2s bs ai (mba m)
      }
    where
      bs : List b
      bs = Map.keys (implicitEmpty (Map.lookup ai (mab m)))

{-# COMPILE AGDA2HS PairMap #-}
{-# COMPILE AGDA2HS lookupA #-}
{-# COMPILE AGDA2HS lookupB #-}
{-# COMPILE AGDA2HS lookupAB #-}
{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS deleteA #-}
