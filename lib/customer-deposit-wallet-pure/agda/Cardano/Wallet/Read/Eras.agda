{-# OPTIONS --erasure #-}

-- Synchronized manually with the corresponding Haskell module.
module Cardano.Wallet.Read.Eras where

open import Haskell.Prelude

{-----------------------------------------------------------------------------
    Eras
------------------------------------------------------------------------------}
Byron = ⊤
Shelley = ⊤
Allegra = ⊤
Mary = ⊤
Alonzo = ⊤
Babbage = ⊤
Conway = ⊤

postulate
  IsEra : Set → Set
  instance
    IsEraByron : IsEra Byron
    IsEraShelley : IsEra Byron
    IsEraAllegra : IsEra Byron
    IsEraMary : IsEra Byron
    IsEraAlonzo : IsEra Byron
    IsEraBabbage : IsEra Byron
    IsEraConway : IsEra Byron
