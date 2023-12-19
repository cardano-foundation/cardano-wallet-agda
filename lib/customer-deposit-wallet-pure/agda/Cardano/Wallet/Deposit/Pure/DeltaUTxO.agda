{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.DeltaUTxO where

open import Haskell.Prelude hiding
    ( null
    )

open import Cardano.Wallet.Deposit.Pure.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Read using
    ( TxIn
    )

postulate
  DeltaUTxO : Set
  null      : DeltaUTxO → Bool

  excludingD : UTxO → List TxIn → (DeltaUTxO × UTxO)
  receiveD   : UTxO → UTxO → (DeltaUTxO × UTxO)

  instance
    iSemigroupDeltaUTxO : Semigroup DeltaUTxO
    iMonoidDeltaUTxO : Monoid DeltaUTxO
