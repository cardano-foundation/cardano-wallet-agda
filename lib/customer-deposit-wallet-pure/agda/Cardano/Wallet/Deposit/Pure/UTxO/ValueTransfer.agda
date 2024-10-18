module Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Read using
    ( Value
      ; iIsLawfulSemigroupValue
      ; iIsLawfulMonoidValue
      ; prop-Value-<>-comm
    )

import Cardano.Wallet.Read as Read

{-----------------------------------------------------------------------------
    ValueTransfer
------------------------------------------------------------------------------}
-- | Records a transfer of 'Value'
-- — some 'Value' is spent, while other 'Value' is received.
record ValueTransfer : Set where
  constructor ValueTransferC
  field
    spent    : Value
    received : Value

open ValueTransfer public

postulate instance
  iEqValueTransfer : Eq ValueTransfer
  iShowValueTransfer : Show ValueTransfer

{-# COMPILE AGDA2HS iEqValueTransfer derive #-}
{-# COMPILE AGDA2HS iShowValueTransfer derive #-}

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

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
instance
  
  iIsLawfulSemigroupValueTransfer : IsLawfulSemigroup ValueTransfer
  iIsLawfulSemigroupValueTransfer .associativity x y z
    rewrite associativity iIsLawfulSemigroupValue (spent x) (spent y) (spent z)
    rewrite associativity iIsLawfulSemigroupValue (received x) (received y) (received z)
    = refl

  iIsLawfulMonoidValueTransfer : IsLawfulMonoid ValueTransfer
  iIsLawfulMonoidValueTransfer .rightIdentity x
    rewrite rightIdentity iIsLawfulMonoidValue (spent x)
    rewrite rightIdentity iIsLawfulMonoidValue (received x)
    = refl 

  iIsLawfulMonoidValueTransfer .leftIdentity x
    rewrite leftIdentity iIsLawfulMonoidValue (spent x)
    rewrite leftIdentity iIsLawfulMonoidValue (received x)
    = refl

  iIsLawfulMonoidValueTransfer .concatenation [] = refl
  iIsLawfulMonoidValueTransfer .concatenation (x ∷ xs)
    rewrite ++-[] (x ∷ xs)
      | concatenation xs
    = refl

-- |
-- 'ValueTransfer' is a commutative semigroup.
-- 
prop-ValueTansfer-<>-comm
  : ∀ (x y : ValueTransfer)
  → x <> y ≡ y <> x
--
prop-ValueTansfer-<>-comm x y
  rewrite prop-Value-<>-comm (spent x) (spent y)
  rewrite prop-Value-<>-comm (received x) (received y)
  = refl
