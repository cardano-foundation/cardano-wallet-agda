module Haskell.Data.Maps.Maybe where

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

-- $prop-unionWith-sym
-- #prop-unionWith-sym#
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
