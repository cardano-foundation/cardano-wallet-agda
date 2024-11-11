module Haskell.Data.Maps.Maybe where

import Prelude hiding (null, subtract)

update :: (a -> Maybe a) -> Maybe a -> Maybe a
update f Nothing = Nothing
update f (Just x) = f x

filter :: (a -> Bool) -> Maybe a -> Maybe a
filter p Nothing = Nothing
filter p (Just x) = if p x then Just x else Nothing

unionWith :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
unionWith f Nothing my = my
unionWith f (Just x) Nothing = Just x
unionWith f (Just x) (Just y) = Just (f x y)

-- |
-- Left-biased union.
union :: Maybe a -> Maybe a -> Maybe a
union = unionWith (\x y -> x)

intersectionWith :: (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
intersectionWith f (Just x) (Just y) = Just (f x y)
intersectionWith _ _ _ = Nothing

-- * Properties

-- $prop-filt-||
-- #p:prop-filt-||#
--
-- [prop-filt-||]:
--
--     Since 'union' is left-biased,
--     filtering commutes with union if the predicate is constant.
--
--     If the predicate is not constant, there are counterexamples.
--
--     @
--     prop-filt-||
--       : ∀ (x y : Bool) {m : Maybe a}
--       → filt (x || y) m
--         ≡ union (filt x m) (filt y m)
--     @

-- $prop-filter-filt
-- #p:prop-filter-filt#
--
-- [prop-filter-filt]:
--
--     'filt' is a special case of 'filter'.
--
--     @
--     prop-filter-filt
--       : ∀ (b : Bool) (m : Maybe a)
--       → filter (λ x → b) m
--         ≡ filt b m
--     @

-- $prop-filter-union
-- #p:prop-filter-union#
--
-- [prop-filter-union]:
--
--     Since 'union' is left-biased,
--     filtering commutes with union if the predicate is constant.
--
--     If the predicate is not constant, there are counterexamples.
--
--     @
--     prop-filter-union
--       : ∀ (p : a → Bool) {m1 m2 : Maybe a}
--       → (∀ (x y : a) → p x ≡ p y)
--       → filter p (union m1 m2)
--         ≡ union (filter p m1) (filter p m2)
--     @

-- $prop-union-sym
-- #p:prop-union-sym#
--
-- [prop-union-sym]:
--     'union' is symmetric if at most one argument is 'Just'.
--
--     @
--     prop-union-sym
--       : ∀ {ma mb : Maybe a}
--       → disjoint ma mb ≡ True
--       → union ma mb ≡ union mb ma
--     @

-- $prop-unionWith-sym
-- #p:prop-unionWith-sym#
--
-- [prop-unionWith-sym]:
--     'unionWith' is symmetric if we 'flip' the function.
--     Note that 'union' is left-biased, not symmetric.
--
--     @
--     prop-unionWith-sym
--       : ∀ {f : a → a → a} {ma mb : Maybe a}
--       → unionWith f ma mb ≡ unionWith (flip f) mb ma
--     @
