{-# OPTIONS --erasure #-}

-- Synchronized manually with the corresponding Haskell module.
module Cardano.Wallet.Read.Tx where

open import Haskell.Prelude

open import Haskell.Data.Map using
    ( Map
    )
open import Haskell.Data.Set using
    ( ℙ
    )
open import Haskell.Data.Word using
    ( Word16
    )
open import Cardano.Wallet.Read.Eras using
    ( IsEra
    )
open import Cardano.Wallet.Read.Value using
    ( Value
    )
import Haskell.Data.ByteString as BS

{-----------------------------------------------------------------------------
    TxId
------------------------------------------------------------------------------}
postulate
  TxId : Set

  instance
    iEqTxId : Eq TxId
    iOrdTxId : Ord TxId

    iLawfulEqTxId : IsLawfulEq TxId

{-----------------------------------------------------------------------------
    TxIx
------------------------------------------------------------------------------}
record TxIx : Set where
  constructor TxIxC
  field
    word16FromTxIx : Word16

open TxIx public

instance
  iEqTxIx : Eq TxIx
  iEqTxIx ._==_ x y = word16FromTxIx x == word16FromTxIx y

  iOrdTxIx : Ord TxIx
  iOrdTxIx =
    ordFromCompare (λ x y → compare (word16FromTxIx x) (word16FromTxIx y))

{-----------------------------------------------------------------------------
    TxIn
------------------------------------------------------------------------------}
record TxIn : Set where
  constructor TxInC
  field
    inputId : TxId
    inputIx : TxIx

open TxIn public

instance
  iEqTxIn : Eq TxIn
  iEqTxIn ._==_ x y = inputId x == inputId y && inputIx x == inputIx y

postulate instance
  iOrdTxIn : Ord TxIn

{-----------------------------------------------------------------------------
    TxOut
------------------------------------------------------------------------------}
CompactAddr = BS.ByteString

postulate
  TxOut : Set

  getCompactAddr : TxOut → CompactAddr
  getValue : TxOut → Value
  mkBasicTxOut : CompactAddr → Value → TxOut

  prop-getCompactAddr-mkBasicTxOut
    : ∀ (addr : CompactAddr)
        (value : Value)
    → getCompactAddr (mkBasicTxOut addr value) ≡ addr

{-----------------------------------------------------------------------------
    Tx
------------------------------------------------------------------------------}
postulate
  Tx : Set → Set

  getTxId : ∀{era} → {{IsEra era}} → Tx era → TxId
  getInputs : ∀{era} → {{IsEra era}} → Tx era → ℙ TxIn
  utxoFromEraTx : ∀{era} → {{IsEra era}} → Tx era → Map TxIn TxOut
