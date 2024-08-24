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
    iIsEraByron : IsEra Byron
    iIsEraShelley : IsEra Byron
    iIsEraAllegra : IsEra Byron
    iIsEraMary : IsEra Byron
    iIsEraAlonzo : IsEra Byron
    iIsEraBabbage : IsEra Byron
    iIsEraConway : IsEra Byron
