{-# OPTIONS --erasure #-}

module Haskell.Data.Maps.Maybe
    {-
    This module adds functions for the 'Maybe' type
    that are analogous to the functions in 'Data.Map'.
    This is used to make proofs for 'Data.Map' more transparent.
    -} where

open import Haskell.Prelude hiding (null; map; filter)

open import Haskell.Data.Maybe using
    ( isJust
    )

{-----------------------------------------------------------------------------
    Data.Maybe
    Functions
------------------------------------------------------------------------------}

update : (a → Maybe a) → Maybe a → Maybe a
update f Nothing = Nothing
update f (Just x) = f x

filter : (a → Bool) → Maybe a → Maybe a
filter p Nothing = Nothing
filter p (Just x) = if p x then Just x else Nothing

unionWith : (a → a → a) → Maybe a → Maybe a → Maybe a
unionWith f Nothing my = my
unionWith f (Just x) Nothing = Just x
unionWith f (Just x) (Just y) = Just (f x y)

union : Maybe a → Maybe a → Maybe a
union = unionWith (λ x y → x)

intersectionWith : (a → b → c) → Maybe a → Maybe b → Maybe c
intersectionWith f (Just x) (Just y) = Just (f x y)
intersectionWith _ _ _ = Nothing

{-# COMPILE AGDA2HS update #-}
{-# COMPILE AGDA2HS filter #-}
{-# COMPILE AGDA2HS unionWith #-}
{-# COMPILE AGDA2HS union #-}
{-# COMPILE AGDA2HS intersectionWith #-}

{-----------------------------------------------------------------------------
    Data.Maybe
    Properties
------------------------------------------------------------------------------}

prop-union-empty-right
  : ∀ {ma : Maybe a}
  → union ma Nothing ≡ ma
prop-union-empty-right {_} {Nothing} = refl
prop-union-empty-right {_} {Just x} = refl

prop-union-assoc
  : ∀ {ma mb mc : Maybe a}
  → union (union ma mb) mc ≡ union ma (union mb mc)
prop-union-assoc {_} {Nothing} {mb} {mc} = refl
prop-union-assoc {_} {Just x} {Nothing} {mc} = refl
prop-union-assoc {_} {Just x} {Just y} {Nothing} = refl
prop-union-assoc {_} {Just x} {Just y} {Just z} = refl
