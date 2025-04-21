{-# OPTIONS --rewriting #-}

module EverythingBags where

import Haskell.Prim.Monad.Extra
import Haskell.Prim.Alternative
import Haskell.Prim.MonadPlus

import Haskell.Law.Extensionality
import Haskell.Law.Monad.Extra
import Haskell.Law.MonadPlus

import Haskell.Prim.Type -- temporary

import Data.Bag
import Data.Indexed

import Data.Map.Prop.Extra
import Data.Monoid.Morphism
import Data.Monoid.Refinement
