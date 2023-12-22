{-# OPTIONS --erasure #-}

module Haskell.Data.ByteString
    {-
    ; ByteString
    -}
    where

open import Haskell.Prelude hiding (lookup; null; map)

{-----------------------------------------------------------------------------
    ByteString
------------------------------------------------------------------------------}

Word8 = Nat
ByteString = List Word8
