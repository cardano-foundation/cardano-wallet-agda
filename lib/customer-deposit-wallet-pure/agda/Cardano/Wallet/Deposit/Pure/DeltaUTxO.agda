{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.DeltaUTxO where

open import Haskell.Prelude hiding
    ( null
    )
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Read using
    ( TxIn
    )

import Cardano.Wallet.Deposit.Pure.UTxO as UTxO
import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    Helper functions
------------------------------------------------------------------------------}
--
prop-reflect-&& 
  : ∀ (x y : Bool)
  → (x && y) ≡ True
  → (x ≡ True) ⋀ (y ≡ True)
--
prop-reflect-&& True y refl = refl `and` refl

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

appendDeltaUTxO : DeltaUTxO → DeltaUTxO → DeltaUTxO
appendDeltaUTxO da db = record
    { excluded = Set.union (excluded da) (excluded'db)
    ; received = UTxO.union (received'da) (received db)
    }
  where
    received'da = UTxO.excluding (received da) (excluded db)
    excluded'db = UTxO.excludingS (excluded db) (received da)

instance
  iSemigroupDeltaUTxO : Semigroup DeltaUTxO
  iSemigroupDeltaUTxO = record { _<>_ = appendDeltaUTxO }

instance
  iMonoidDeltaUTxO : Monoid DeltaUTxO
  iMonoidDeltaUTxO =
    record {DefaultMonoid (λ where .DefaultMonoid.mempty → empty)}

{-# COMPILE AGDA2HS DeltaUTxO #-}
{-# COMPILE AGDA2HS null #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS apply #-}
{-# COMPILE AGDA2HS excludingD #-}
{-# COMPILE AGDA2HS receiveD #-}
{-# COMPILE AGDA2HS appendDeltaUTxO #-}
{-# COMPILE AGDA2HS iSemigroupDeltaUTxO #-}
{-# COMPILE AGDA2HS iMonoidDeltaUTxO #-}

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
    lem1 = projl (prop-reflect-&& _ _ eq)

    lem2 : Map.null (received du) ≡ True
    lem2 = projr (prop-reflect-&& _ _ eq)

--
@0 prop-apply-empty
  : ∀ (u : UTxO) (key : TxIn)
  → Map.lookup key (apply empty u) ≡ Map.lookup key u 
--
prop-apply-empty u key =
  begin
    Map.lookup key (apply empty u)
  ≡⟨ UTxO.prop-union-empty key _ ⟩
    Map.lookup key (UTxO.excluding u (excluded empty))
  ≡⟨ UTxO.prop-excluding-empty key u ⟩
    Map.lookup key u 
  ∎
