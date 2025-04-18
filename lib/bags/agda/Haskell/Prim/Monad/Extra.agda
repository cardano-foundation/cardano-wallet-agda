
-- Extra functions that should be in Control.Monad

module Haskell.Prim.Monad.Extra where

open import Haskell.Prim
open import Haskell.Prim.Monad

join : ⦃ Monad m ⦄ → m (m a) → m a
join x = x >>= id
