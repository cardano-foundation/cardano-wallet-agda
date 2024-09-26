{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.UTxO.UTxO
    {-
    ; UTxO
      ; null
      ; empty
      ; dom
      ; balance
      ; union
      ; excluding
      ; restrictedBy
      ; excludingS
      ; filterByAddress
    -}
    where

open import Haskell.Prelude hiding (null; f)

open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; TxIn
    ; TxOut
      ; getCompactAddr
      ; getValue
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
{-|
The type 'UTxO' is used to keep track of unspent transaction outputs.
This type is a mapping from transaction inputs, 'TxIn',
which are references, to transaction outputs, 'TxOut',
which record the actual currency values, addresses, and other data,
that is available for spending.
-}
UTxO : Set
UTxO = Map.Map TxIn TxOut

-- | Test whether the 'UTxO' is empty.
null : UTxO → Bool
null = Map.null

-- | The empty 'UTxO'.
empty : UTxO
empty = Map.empty

-- | The domain of a 'UTxO' is the set of /inputs/.
dom : UTxO → Set.ℙ TxIn
dom = Map.keysSet

-- | The total value contained in the outputs.
balance : UTxO → Value
balance = foldMap getValue

-- | Left-biased union.
union : UTxO → UTxO → UTxO
union = Map.unionWith (λ x y → x)

-- | Infix synonym for 'union'.
-- (Not exported to Haskell.)
_∪_ : UTxO → UTxO → UTxO
_∪_ = union

-- | Exclude a set of inputs.
excluding : UTxO → Set.ℙ TxIn → UTxO
excluding = Map.withoutKeys

-- | Infix synonym for 'excluding'.
-- (Not exported to Haskell.)
_⋪_ : Set.ℙ TxIn → UTxO → UTxO
_⋪_ x u = excluding u x

-- | Restrict to a given set of inputs.
restrictedBy : UTxO → Set.ℙ TxIn → UTxO
restrictedBy = Map.restrictKeys

-- | Exclude the inputs of a 'UTxO' from a 'Set' of inputs.
excludingS : Set.ℙ TxIn → UTxO → Set.ℙ TxIn
excludingS s utxo = Set.filter (not ∘ (λ txin → Map.member txin utxo)) s

-- | Keep those outputs whose address satisfies the predicate.
filterByAddress : (Address → Bool) → UTxO → UTxO
filterByAddress p = Map.filter (p ∘ getCompactAddr)

{-# COMPILE AGDA2HS UTxO #-}
{-# COMPILE AGDA2HS null #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS dom #-}
{-# COMPILE AGDA2HS balance #-}
{-# COMPILE AGDA2HS union #-}
{-# COMPILE AGDA2HS excluding #-}
{-# COMPILE AGDA2HS restrictedBy #-}
{-# COMPILE AGDA2HS excludingS #-}
{-# COMPILE AGDA2HS filterByAddress #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}
-- |
-- 'empty' is a left identity of 'union'.
--
prop-union-empty-left
  : ∀ {utxo : UTxO}
  → union empty utxo ≡ utxo
--
prop-union-empty-left = Map.prop-union-empty-left

-- |
-- 'empty' is a right identity of 'union'.
--
prop-union-empty-right
  : ∀ {utxo : UTxO}
  → union utxo empty ≡ utxo
--
prop-union-empty-right = Map.prop-union-empty-right

-- |
-- Excluding the empty set does nothing.
--
@0 prop-excluding-empty
  : ∀ (utxo : UTxO)
  → excluding utxo Set.empty ≡ utxo
--
prop-excluding-empty utxo =
  Map.prop-equality (λ key → Map.prop-withoutKeys-empty key utxo)

-- |
-- 'union' is associative.
--
prop-union-assoc
  : ∀ {ua ub uc : UTxO}
  → (ua ∪ ub) ∪ uc ≡ ua ∪ (ub ∪ uc)
--
prop-union-assoc = Map.prop-union-assoc

-- |
-- Excluding from a union is the same as excluding
-- from each member of the union.
--
postulate
 prop-excluding-union
  : ∀ (x : Set.ℙ TxIn) (ua ub : UTxO)
  → x ⋪ (ua ∪ ub) ≡ (x ⋪ ua) ∪ (x ⋪ ub)
--

-- |
-- Excluding from an exclusion is the same as excluding the union.
--
postulate
 prop-excluding-excluding
  : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
  → x ⋪ (y ⋪ utxo) ≡ (Set.union x y) ⋪ utxo
--

-- |
-- Excluding the intersection is the same as the union of the exclusions.
--
@0 prop-excluding-intersection
  : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
  → (Set.intersection x y) ⋪ utxo ≡ (x ⋪ utxo) ∪ (y ⋪ utxo)
--
prop-excluding-intersection {x} {y} {utxo} =
  Map.prop-withoutKeys-intersection utxo x y

-- |
-- Excluding the entire domain gives the empty 'UTxO'.
--
postulate
 prop-excluding-dom
  : ∀ {utxo : UTxO}
  → dom utxo ⋪ utxo ≡ empty
--

-- |
-- Excluding two sets of 'TxIn's can be done in either order.
--
prop-excluding-sym
  : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
  → x ⋪ (y ⋪ utxo) ≡ y ⋪ (x ⋪ utxo)
--
prop-excluding-sym {x} {y} {utxo} =
  begin
    x ⋪ (y ⋪ utxo)
  ≡⟨ prop-excluding-excluding ⟩
    (Set.union x y) ⋪ utxo
  ≡⟨ cong (λ o → o ⋪ utxo) (Set.prop-union-sym) ⟩
    (Set.union y x) ⋪ utxo
  ≡⟨ sym prop-excluding-excluding ⟩
    y ⋪ (x ⋪ utxo)
  ∎

-- |
-- Not excluding inputs makes no difference if these
-- inputs have nothing in common with the 'UTxO'.
--
postulate
 prop-excluding-excludingS
  : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
  → Set.intersection (dom ua) (dom ub) ≡ Set.empty
  → (excludingS x ua) ⋪ ub ≡ x ⋪ ub
--

-- |
-- Those outputs whose address satisfies the predicate are kept.
--
prop-filterByAddress-filters
    : ∀ (p : Address → Bool)
        (utxo : UTxO) (txin : TxIn) (txout : TxOut)
    → Map.lookup txin utxo ≡ Just txout
    → Map.member txin (filterByAddress p utxo)
        ≡ p (getCompactAddr txout)
--
prop-filterByAddress-filters p utxo key x eq =
    begin
        isJust (Map.lookup key (filterByAddress p utxo))
    ≡⟨ cong isJust (Map.prop-lookup-filterWithKey-Just key x utxo q eq) ⟩
        isJust (if p (getCompactAddr x) then Just x else Nothing)
    ≡⟨ lem2 _ _ ⟩
        p (getCompactAddr x)
    ∎
  where
    q : TxIn → _
    q k = p ∘ getCompactAddr

    lem2
      : ∀ {a : Set} (b : Bool) (x : a)
      → isJust (if b then Just x else Nothing) ≡ b
    lem2 True x = refl
    lem2 False x = refl
