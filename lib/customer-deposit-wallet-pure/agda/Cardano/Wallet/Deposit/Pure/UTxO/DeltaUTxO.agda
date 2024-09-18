{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.UTxO.DeltaUTxO
    {-
    ; DeltaUTxO
      ; null
      ; empty
      ; apply
      ; excludingD
      ; receiveD
      ; instance Semigroup DeltaUTxO
      ; instance Monoid DeltaUTxO
    -}
    where

open import Haskell.Prelude hiding
    ( null
    )
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Read using
    ( TxIn
    )

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    DeltaUTxO
------------------------------------------------------------------------------}
record DeltaUTxO : Set where
  field
    excluded : Set.ℙ TxIn
    received : UTxO

open DeltaUTxO public

null : DeltaUTxO → Bool
null du = Set.null (excluded du) && UTxO.null (received du)

empty : DeltaUTxO
empty = record
  { excluded = Set.empty
  ; received = Map.empty
  }

apply : DeltaUTxO → UTxO → UTxO
apply du utxo =
   UTxO.union (UTxO.excluding utxo (excluded du)) (received du)

excludingD : UTxO → Set.ℙ TxIn → (DeltaUTxO × UTxO)
excludingD utxo txins =
    (du , UTxO.excluding utxo txins)
  where
    du = record
      { excluded = Set.difference (Map.keysSet utxo) txins
      ; received = UTxO.empty
      }

receiveD : UTxO → UTxO → (DeltaUTxO × UTxO)
receiveD old new =
    (du , UTxO.union old new)
  where
    du = record 
      { excluded = Set.empty
      ; received = new
      }

-- | Apply `x` *after* `y`.
append : DeltaUTxO → DeltaUTxO → DeltaUTxO
append x y = record
    { excluded = Set.union (excluded'x) (excluded y)
    ; received = UTxO.union (received x) (received'y)
    }
  where
    excluded'x = UTxO.excludingS (excluded x) (received y)
    received'y = UTxO.excluding (received y) (excluded x)

{-# COMPILE AGDA2HS DeltaUTxO #-}
{-# COMPILE AGDA2HS null #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS apply #-}
{-# COMPILE AGDA2HS excludingD #-}
{-# COMPILE AGDA2HS receiveD #-}
{-# COMPILE AGDA2HS append #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
lemma-intro-DeltaUTxO-≡
  : ∀ {a : Set.ℙ TxIn} {b : UTxO} (dd : DeltaUTxO)
  → excluded dd ≡ a
  → received dd ≡ b
  → dd ≡ record { excluded = a; received = b }
lemma-intro-DeltaUTxO-≡ dd refl refl = refl

--
prop-null-empty
  : ∀ (du : DeltaUTxO)
  → null du ≡ True
  → du ≡ empty
--
prop-null-empty du eq =
    lemma-intro-DeltaUTxO-≡
      du
      (Set.prop-null-empty (excluded du) lem1)
      (Map.prop-null-empty (received du) lem2)
  where
    lem1 : Set.null (excluded du) ≡ True
    lem1 = projl (prop-&&-⋀ eq)

    lem2 : Map.null (received du) ≡ True
    lem2 = projr (prop-&&-⋀ eq)
