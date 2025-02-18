{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Data.Function.Law
    ( -- $prop-==-Injective
    )
where

import Prelude hiding (null, subtract)

dummy :: ()
dummy = ()

-- * Properties

-- $prop-==-Injective
-- #p:prop-==-Injective#
--
-- [prop-==-Injective]:
--     Injective functions preserve equality.
--
--     > prop-==-Injective
--     >   : ∀ ⦃ _ : Eq a ⦄ ⦃ _ : IsLawfulEq a ⦄
--     >       ⦃ _ : Eq b ⦄ ⦃ _ : IsLawfulEq b ⦄
--     >   → ∀ (f : a → b) → Injective f
--     >   → ∀ (x y : a)
--     >   → (x == y)
--     >     ≡ (f x == f y)
