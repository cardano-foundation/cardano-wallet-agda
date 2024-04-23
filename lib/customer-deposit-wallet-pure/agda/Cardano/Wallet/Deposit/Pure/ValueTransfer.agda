module Cardano.Wallet.Deposit.Pure.ValueTransfer where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Read using
    ( Value
    )

import Cardano.Wallet.Deposit.Read as Read

{-----------------------------------------------------------------------------
    ValueTransfer
------------------------------------------------------------------------------}

record ValueTransfer : Set where
  field
    spent    : Value
    received : Value

open ValueTransfer public

fromSpent : Value → ValueTransfer
fromSpent = λ value → record { spent = value ; received = mempty }

fromReceived : Value → ValueTransfer
fromReceived = λ value → record { spent = mempty ; received = value }

instance
  iSemigroupValueTansfer : Semigroup ValueTransfer
  _<>_ {{iSemigroupValueTansfer}} =
    λ v1 v2 → record
        { spent = spent v1 <> spent v2
        ; received = received v1 <> received v2
        }

  iMonoidValueTransfer : Monoid ValueTransfer
  iMonoidValueTransfer =
    record { DefaultMonoid
        (λ where .DefaultMonoid.mempty → record { spent = mempty ; received = mempty })
    }

{-# COMPILE AGDA2HS ValueTransfer #-}
{-# COMPILE AGDA2HS fromSpent #-}
{-# COMPILE AGDA2HS fromReceived #-}
{-# COMPILE AGDA2HS iSemigroupValueTansfer #-}
{-# COMPILE AGDA2HS iMonoidValueTransfer #-}
