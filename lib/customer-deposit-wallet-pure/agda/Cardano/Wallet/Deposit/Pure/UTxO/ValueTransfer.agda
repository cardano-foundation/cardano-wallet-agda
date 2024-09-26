module Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer where

open import Haskell.Prelude

open import Cardano.Wallet.Deposit.Read using
    ( Value
    )

import Cardano.Wallet.Deposit.Read as Read

{-----------------------------------------------------------------------------
    ValueTransfer
------------------------------------------------------------------------------}
-- | Records a transfer of 'Value'
-- — some 'Value' is spent, while other 'Value' is received.
record ValueTransfer : Set where
  field
    spent    : Value
    received : Value

open ValueTransfer public

-- | Record spending a given 'Value'.
fromSpent : Value → ValueTransfer
fromSpent = λ value → record { spent = value ; received = mempty }

-- | Record receiving a given 'Value'.
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
