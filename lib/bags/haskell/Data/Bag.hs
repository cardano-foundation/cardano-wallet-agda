{-# LANGUAGE StandaloneDeriving #-}

module Data.Bag
    ( Bag
    )
where

-- |
-- A unordered, finite collection of items.
-- Items may appear more than once.
--
-- Bag is the free commutative monoid.
data Bag a = MkBag {elements :: [a]}

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
