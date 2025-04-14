{-# LANGUAGE StandaloneDeriving #-}

module Data.Bag
    ( -- * Data

      -- ** Bag Type
      Bag

      -- ** Construction
    , empty
    , singleton
    , fromList
    , guard

      -- ** Query
    , member

      -- ** Combine
    , union

      -- ** Filter
    , filter
      -- $prop-filter-guard

      -- * Properties
    )
where

import Prelude hiding (filter)

-- |
-- A unordered, finite collection of items.
-- Items may appear more than once.
--
-- Bag is the free commutative monoid.
data Bag a = MkBag {elements :: [a]}

-- |
-- The empty 'Bag'.
empty :: Bag a
empty = MkBag []

-- |
-- 'Bag' with a single element.
singleton :: a -> Bag a
singleton x = MkBag [x]

-- |
-- Create a 'Bag' from a list of items.
fromList :: [a] -> Bag a
fromList = MkBag

-- |
-- Return a 'Bag' with one element if the condition is 'True',
-- and 'empty' if the condition is 'False'.
-- Very useful for @do@ notation.
--
-- From "Control.Monad".
guard :: Bool -> Bag ()
guard True = singleton ()
guard False = empty

-- |
-- Is the item in the 'Bag'?
member :: Eq a => a -> Bag a -> Bool
member x (MkBag xs) = elem x xs

-- |
-- Delete the first occurrence of an item from the list.
-- Return 'Nothing' if the element does not occur.
delete1 :: Eq a => a -> [a] -> Maybe [a]
delete1 x [] = Nothing
delete1 x (y : ys) =
    if x == y then Just ys else fmap (y :) (delete1 x ys)

-- |
-- Two lists are equal as bags.
eqBag :: Eq a => [a] -> [a] -> Bool
eqBag [] [] = True
eqBag [] (y : ys) = False
eqBag (x : xs) ys' =
    case delete1 x ys' of
        Just ys -> eqBag xs ys
        Nothing -> False

deriving instance (Eq a) => Eq (Bag a)

instance Functor Bag where
    fmap f (MkBag xs) = MkBag (fmap f xs)

instance Applicative Bag where
    pure = \x -> MkBag (pure x)
    (<*>) = \fs xs -> MkBag (elements fs <*> elements xs)
    (<*) = \fs xs -> MkBag (elements fs <* elements xs)
    (*>) = \fs xs -> MkBag (elements fs *> elements xs)

instance Monad Bag where
    MkBag m >>= f = MkBag (m >>= (\r -> elements r) . f)

-- |
-- The union of two 'Bag's contains all items from each of the 'Bag's.
--
-- 'union' is commutative.
union :: Bag a -> Bag a -> Bag a
union (MkBag xs) (MkBag ys) = MkBag (xs <> ys)

instance Semigroup (Bag a) where
    (<>) = union

instance Monoid (Bag a) where
    mempty = empty

-- |
-- Filter all elements that satisfy the predicate.
filter :: (a -> Bool) -> Bag a -> Bag a
filter =
    \p xs ->
        do
            x <- xs
            guard (p x)
            pure x

-- * Properties

-- $prop-filter-guard
-- #p:prop-filter-guard#
--
-- [prop-filter-guard]:
--     'filter' can be written using @do@ notation with a 'guard'.
--
--     > prop-filter-guard
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄ (p : a → Bool) (xs : Bag a)
--     >   → (filter p xs
--     >     == (do x ← xs; guard (p x); pure x)) ≡ True
