module Data.Maybe.Extra where

import Prelude hiding (null, subtract)

fromJust :: Maybe a -> a
fromJust Nothing = error "fromJust Nothing"
fromJust (Just x) = x
