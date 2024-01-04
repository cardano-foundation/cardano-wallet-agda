{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.UTxO
    {-
    ; UTxO
    -}
    where

open import Haskell.Prelude hiding (null; f)

open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; TxIn
    ; TxOut
    ; Value
    )
open import Haskell.Data.Maybe using
    ( isJust
    )

import Haskell.Data.Map as Map
import Haskell.Data.Set as Set

{-----------------------------------------------------------------------------
    UTxO
------------------------------------------------------------------------------}

UTxO = Map.Map TxIn TxOut

null : UTxO → Bool
null = Map.null

empty : UTxO
empty = Map.empty

-- | Domain of a 'UTxO' = the set of /inputs/ of the /utxo/.
dom : UTxO → Set.ℙ TxIn
dom = Map.keysSet

balance : UTxO → Value
balance = foldMap TxOut.value

-- | Left-biased union.
union : UTxO → UTxO → UTxO
union = Map.unionWith (λ x y → x)

excluding : UTxO → Set.ℙ TxIn → UTxO
excluding = Map.withoutKeys

-- | Exclude the inputs of a 'UTxO' from a 'Set' of inputs.
excludingS : Set.ℙ TxIn → UTxO → Set.ℙ TxIn
excludingS s utxo = Set.filter (not ∘ (λ txin → Map.member txin utxo)) s

filterByAddress : (Address → Bool) → UTxO → UTxO
filterByAddress p = Map.filter (p ∘ TxOut.address)

{-# COMPILE AGDA2HS UTxO #-}
{-# COMPILE AGDA2HS null #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS dom #-}
{-# COMPILE AGDA2HS balance #-}
{-# COMPILE AGDA2HS union #-}
{-# COMPILE AGDA2HS excluding #-}
{-# COMPILE AGDA2HS excludingS #-}
{-# COMPILE AGDA2HS filterByAddress #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
--
prop-union-empty
  : ∀ (key : TxIn) (u : UTxO)
  → Map.lookup key (union u empty)
    ≡ Map.lookup key u
--
prop-union-empty key u =
    begin
      Map.lookup key (union u empty)
    ≡⟨ Map.prop-lookup-unionWith key u empty f ⟩
      Map.unionWithMaybe f (Map.lookup key u) (Map.lookup key empty)
    ≡⟨ cong (Map.unionWithMaybe f (Map.lookup key u)) (Map.prop-lookup-empty key)⟩
      Map.unionWithMaybe f (Map.lookup key u) Nothing
    ≡⟨ lem1 (Map.lookup key u) ⟩
      Map.lookup key u
    ∎
  where
    f = (λ x y → x)

    lem1 : (ma : Maybe TxOut) → Map.unionWithMaybe f ma Nothing ≡ ma
    lem1 (Just x) = refl
    lem1 Nothing = refl

--
@0 prop-excluding-empty
  : ∀ (key : TxIn) (u : UTxO)
  → Map.lookup key (excluding u Set.empty)
    ≡ Map.lookup key u
--
prop-excluding-empty key u = Map.prop-withoutKeys-empty key u

--
prop-filterByAddress-filters
    : ∀ (p : Address → Bool)
        (utxo : UTxO) (txin : TxIn) (txout : TxOut)
    → Map.lookup txin utxo ≡ Just txout
    → Map.member txin (filterByAddress p utxo)
        ≡ p (TxOut.address txout)
--
prop-filterByAddress-filters p u key x eq =
    begin
        isJust (Map.lookup key (filterByAddress p u))
    ≡⟨ cong isJust (Map.prop-lookup-filterWithKey-Just key x u q eq) ⟩
        isJust (if p (TxOut.address x) then Just x else Nothing)
    ≡⟨ lem2 _ _ ⟩
        p (TxOut.address x)
    ∎
  where
    q : TxIn → _
    q k = p ∘ TxOut.address

    lem2
      : ∀ {a : Set} (b : Bool) (x : a)
      → isJust (if b then Just x else Nothing) ≡ b
    lem2 True x = refl
    lem2 False x = refl
