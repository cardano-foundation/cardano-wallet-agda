module Data.List.Law
    ( -- * List transformations
      -- $prop-elem-map

      -- * Searching lists

      -- ** Searching by equality
      -- $prop-elem-/=
      -- $prop-elem-nub
      -- $prop-elem-deleteAll

      -- ** Searching with a predicate
      -- $prop-filter-sym
      -- $prop-filter-filter

      -- * Special lists

      -- ** \"Set\" operations
      -- $prop-nub-empty
      -- $prop-nub-::
      -- $prop-nub-nub
      isDeduplicated
      -- $prop-isDeduplicated-empty
      -- $prop-isDeduplicated-::
      -- $prop-isDeduplicated
      -- $prop-isDeduplicated-nub
      -- $prop-isDeduplicated-map
    , deleteAll
      -- $prop-deleteAll
      -- $prop-deleteAll-==
      -- $prop-deleteAll-deleteAll
      -- $prop-map-deleteAll

      -- ** Ordered lists
    , isSorted
    )
where

import Prelude hiding (null, subtract)

-- |
-- Remove /all/ occurrences of the item from the list.
deleteAll :: Eq a => a -> [a] -> [a]
deleteAll x = filter (not . (x ==))

-- |
-- Decide whether a list does not contain duplicated elements.
isDeduplicated :: Eq a => [a] -> Bool
isDeduplicated [] = True
isDeduplicated (x : xs) = not (elem x xs) && isDeduplicated xs

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

-- $prop-deleteAll-==
-- #p:prop-deleteAll-==#
--
-- [prop-deleteAll-==]:
--     Deleting an item will do nothing precisely
--     when the item is not an element.
--
--     > prop-deleteAll-==
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >   → ∀ (x : a) (ys : List a)
--     >   → (deleteAll x ys == ys)
--     >     ≡ not (elem x ys)

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

-- $prop-deleteAll-nub
-- #p:prop-deleteAll-nub#
--
-- [prop-deleteAll-nub]:
--     'deleteAll' commutes with 'nub'.
--
--     > prop-deleteAll-nub
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       (x : a) (xs : List a)
--     >   → deleteAll x (nub xs)
--     >     ≡ nub (deleteAll x xs)

-- $prop-elem-/=
-- #p:prop-elem-/=#
--
-- [prop-elem-/=]:
--     An item which is contained in one of the lists
--     but not in the other, witnesses that the lists are unequal.
--
--     > prop-elem-/=
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       (x : a) (ys zs : List a)
--     >   → (elem x ys /= elem x zs) ≡ True
--     >   → (ys /= zs) ≡ True

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

-- $prop-elem-map
-- #p:prop-elem-map#
--
-- [prop-elem-map]:
--     A mapped item is a member of the mapped list
--     iff it is a member of the original list — if the function is injective.
--
--     > prop-elem-map
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
--     >   → ∀ (f : a → b) → Injective f
--     >   → ∀ (x : a) (ys : List a)
--     >   → elem (f x) (map f ys)
--     >     ≡ elem x ys

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

-- $prop-filter-sym
-- #p:prop-filter-sym#
--
-- [prop-filter-sym]:
--     Two 'filter' can be applied in any order.
--
--     > prop-filter-sym
--     >   : ∀ (p q : a → Bool) (xs : List a)
--     >   → filter p (filter q xs)
--     >     ≡ filter q (filter p xs)

-- $prop-isDeduplicated
-- #p:prop-isDeduplicated#
--
-- [prop-isDeduplicated]:
--     A definition of 'isDeduplicated' in terms of 'nub'.
--
--     > prop-isDeduplicated
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >   → (xs : List a)
--     >   → isDeduplicated xs ≡ (nub xs == xs)

-- $prop-isDeduplicated-::
-- #p:prop-isDeduplicated-::#
--
-- [prop-isDeduplicated-::]:
--     Recursive definition of 'isDeduplicated', non-empty list.
--
--     > prop-isDeduplicated-::
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
--     >   → (x : a) (xs : List a)
--     >   → isDeduplicated (x ∷ xs)
--     >     ≡ (not (elem x xs) && isDeduplicated xs)

-- $prop-isDeduplicated-empty
-- #p:prop-isDeduplicated-empty#
--
-- [prop-isDeduplicated-empty]:
--     Recursive definition of 'isDeduplicated', empty list.
--
--     > prop-isDeduplicated-empty
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
--     >   → isDeduplicated {a} []
--     >     ≡ True

-- $prop-isDeduplicated-map
-- #p:prop-isDeduplicated-map#
--
-- [prop-isDeduplicated-map]:
--     Applying an injective function to a deduplicated list
--     yields a deduplicated list.
--
--     > prop-isDeduplicated-map
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
--     >   → ∀ (f : a → b) → Injective f
--     >   → ∀ (xs : List a)
--     >   → isDeduplicated xs ≡ True
--     >   → isDeduplicated (map f xs) ≡ True

-- $prop-isDeduplicated-nub
-- #p:prop-isDeduplicated-nub#
--
-- [prop-isDeduplicated-nub]:
--     The purpose of 'nub' is to deduplicate a list.
--
--     > prop-isDeduplicated-nub
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       (xs : List a)
--     >   → isDeduplicated (nub xs)
--     >     ≡ True

-- $prop-map-deleteAll
-- #p:prop-map-deleteAll#
--
-- [prop-map-deleteAll]:
--     Deleting an item and mapping with a function
--     is the same as deleting the mapped item —
--     if the function is injective.
--
--     > prop-map-deleteAll
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
--     >   → ∀ (f : a → b) → Injective f
--     >   → ∀ (x : a) (ys : List a)
--     >   → map f (deleteAll x ys)
--     >     ≡ deleteAll (f x) (map f ys)

-- $prop-nub-::
-- #p:prop-nub-::#
--
-- [prop-nub-::]:
--     Recursive definition of 'nub', non-empty list.
--
--     > prop-nub-::
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
--     >   → (x : a) (xs : List a)
--     >   → nub (x ∷ xs)
--     >     ≡ x ∷ deleteAll x (nub xs)

-- $prop-nub-empty
-- #p:prop-nub-empty#
--
-- [prop-nub-empty]:
--     Recursive definition of 'nub', empty list.
--
--     > prop-nub-empty
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄
--     >   → nub {a} []
--     >     ≡ []

-- $prop-nub-nub
-- #p:prop-nub-nub#
--
-- [prop-nub-nub]:
--     Applying 'nub' twice is the same as applying it once.
--
--     > prop-nub-nub
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       (xs : List a)
--     >   → nub (nub xs)
--     >     ≡ nub xs
