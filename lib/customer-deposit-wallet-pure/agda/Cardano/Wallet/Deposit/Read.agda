{-# OPTIONS --erasure #-}
module Cardano.Wallet.Deposit.Read where

open import Haskell.Prelude

import Haskell.Data.ByteString as BS
import Haskell.Data.Map as Map

Addr = BS.ByteString
Address = Addr

instance
  iEqAddress : Eq Address
  iEqAddress = BS.iEqByteString

  iOrdAddress : Ord Address
  iOrdAddress = BS.iOrdByteString

  iLawfulEqAddress : IsLawfulEq Address
  iLawfulEqAddress = BS.iLawfulEqByteString

Slot = Nat

{-# COMPILE AGDA2HS Addr #-}
{-# COMPILE AGDA2HS Address #-}
{-# COMPILE AGDA2HS Slot #-}

{-----------------------------------------------------------------------------
    Value
------------------------------------------------------------------------------}
data Value : Set where
    MkValue : Integer → Value

instance
  iSemigroupValue : Semigroup Value
  _<>_ {{iSemigroupValue}} (MkValue a) (MkValue b) = MkValue (a + b)

  iMonoidValue : Monoid Value
  iMonoidValue =
    record {DefaultMonoid (λ where .DefaultMonoid.mempty → MkValue 0)}

exceeds : Value → Value → Bool
exceeds (MkValue a) (MkValue b) = a >= b

minus : Value → Value → Value
minus (MkValue a) (MkValue b) = MkValue (a - b)

{-# COMPILE AGDA2HS Value #-}
{-# COMPILE AGDA2HS iSemigroupValue #-}
{-# COMPILE AGDA2HS iMonoidValue #-}
{-# COMPILE AGDA2HS exceeds #-}
{-# COMPILE AGDA2HS minus #-}

{-----------------------------------------------------------------------------
    Transactions
------------------------------------------------------------------------------}

TxId = Nat
Ix = Int

TxIn = TxId × Ix

record TxOut : Set where
  constructor TxOutC
  field
    address : Address
    value   : Value

open TxOut public

record Tx : Set where
  constructor TxC
  field
    txid    : TxId
    inputs  : List TxIn
    outputs : List TxOut

open Tx public

{-# COMPILE AGDA2HS TxId #-}
{-# COMPILE AGDA2HS Ix #-}
{-# COMPILE AGDA2HS TxIn #-}
{-# COMPILE AGDA2HS TxOut #-}
{-# COMPILE AGDA2HS Tx #-}
