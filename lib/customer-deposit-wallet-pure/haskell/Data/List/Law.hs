module Data.List.Law
    ( -- * Searching lists

      -- ** Searching by equality
      -- $prop-elem-nub
      -- $prop-elem-deleteAll

      -- ** Searching with a predicate
      -- $prop-filter-filter

      -- * Special lists

      -- ** \"Set\" operations
      isDeduplicated
      -- $prop-isDeduplicated
    , deleteAll
      -- $prop-deleteAll
      -- $prop-deleteAll-deleteAll

      -- ** Ordered lists
    , isSorted
    )
where

import Data.List (nub)
import Prelude hiding (null, subtract)

-- |
-- Decide whether a list does not contain duplicated elements.
isDeduplicated :: Eq a => [a] -> Bool
isDeduplicated xs = nub xs == xs

-- |
-- Remove /all/ occurrences of the item from the list.
deleteAll :: Eq a => a -> [a] -> [a]
deleteAll x = filter (not . (x ==))

-- |
-- Decide whether a list is sorted.
isSorted :: Ord a => [a] -> Bool
isSorted xs = and (zipWith (<=) xs (drop 1 xs))

-- * Properties

-- $prop-deleteAll
-- #p:prop-deleteAll#
--
-- [prop-deleteAll]:
--     Definition of 'deleteAll'.
--
--     > prop-deleteAll
--     >   : ∀ ⦃ _ : Eq a ⦄
--     >       (x : a) (xs : List a)
--     >   → deleteAll x xs
--     >     ≡ filter (not ∘ (x ==_)) xs

-- $prop-deleteAll-deleteAll
-- #p:prop-deleteAll-deleteAll#
--
-- [prop-deleteAll-deleteAll]:
--     Deleting an item twice is the same as deleting the item once.
--
--     > prop-deleteAll-deleteAll
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       (x : a) (ys : List a)
--     >   → deleteAll x (deleteAll x ys)
--     >     ≡ deleteAll x ys

-- $prop-elem-deleteAll
-- #p:prop-elem-deleteAll#
--
-- [prop-elem-deleteAll]:
--     A deleted item is no longer an element.
--
--     > prop-elem-deleteAll
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       (x y : a) (zs : List a)
--     >   → elem x (deleteAll y zs)
--     >     ≡ (if x == y then False else elem x zs)

-- $prop-elem-nub
-- #p:prop-elem-nub#
--
-- [prop-elem-nub]:
--     An item is an element of the 'nub' iff it is
--     an element of the original list.
--
--     > prop-elem-nub
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       (x : a) (ys : List a)
--     >   → elem x (nub ys)
--     >     ≡ elem x ys

-- $prop-filter-filter
-- #p:prop-filter-filter#
--
-- [prop-filter-filter]:
--     Filtering with the same predicate twice is the same
--     als filtering once.
--
--     > prop-filter-filter
--     >   : ∀ (p : a → Bool) (xs : List a)
--     >   → filter p (filter p xs)
--     >     ≡ filter p xs

-- $prop-isDeduplicated
-- #p:prop-isDeduplicated#
--
-- [prop-isDeduplicated]:
--     Definition of 'isDeduplicated'.
--
--     > prop-isDeduplicated
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
--     >   → (xs : List a)
--     >   → isDeduplicated xs ≡ (nub xs == xs)
