{-# LANGUAGE UnicodeSyntax #-}

module Haskell.Data.List where


import qualified Data.List

foldl'
  :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl' = Data.List.foldl'

