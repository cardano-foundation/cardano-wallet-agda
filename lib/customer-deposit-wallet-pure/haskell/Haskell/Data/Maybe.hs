module Haskell.Data.Maybe where

isNothing :: Maybe a -> Bool
isNothing (Just _) = False
isNothing Nothing = True

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing = False

catMaybes :: [Maybe a] -> [a]
catMaybes [] = []
catMaybes (Nothing : xs) = catMaybes xs
catMaybes (Just x : xs) = x : catMaybes xs

fromMaybe :: a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a Nothing = a

