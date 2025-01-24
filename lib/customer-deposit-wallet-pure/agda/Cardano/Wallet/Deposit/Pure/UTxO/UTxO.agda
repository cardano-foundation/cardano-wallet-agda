{-# OPTIONS --erasure #-}

module Cardano.Wallet.Deposit.Pure.UTxO.UTxO
    {-|
    ; UTxO
      ; null
      ; empty
      ; dom
      ; disjoint
        ; prop-disjoint-dom
        ; prop-disjoint-empty
      ; balance
      ; union
        ; prop-union-empty-left
        ; prop-union-empty-right
        ; prop-union-assoc
        ; prop-union-sym
      ; excluding
        ; prop-excluding-empty
        ; prop-excluding-dom
        ; prop-excluding-absorb
        ; prop-excluding-excluding
        ; prop-excluding-sym
        ; prop-excluding-difference
        ; prop-excluding-intersection
        ; prop-excluding-union
      ; restrictedBy
        ; prop-restrictedBy-dom
        ; prop-restrictedBy-disjoint
        ; prop-restrictedBy-union
        ; prop-union-restrictedBy-absorbs
      ; excludingS
        ; prop-excludingS
        ; prop-excluding-excludingS
      ; filterByAddress
        ; prop-filterByAddress-filters
    -}
    where

open import Haskell.Reasoning
open import Haskell.Prelude hiding (null; f)

{-# FOREIGN ADGA2HS
import Prelude hiding (null)
#-}

open import Cardano.Wallet.Deposit.Read.Temp using
    ( Address
    )
open import Cardano.Wallet.Read using
    ( TxIn
    ; TxOut
      ; getCompactAddr
      ; getValue
    ; Value
    )
open import Haskell.Data.Maybe using
    ( isJust
    )

import Data.Map as Map
import Data.Set as Set

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read
    ( TxIn
    , TxOut
    , Value
    , getCompactAddr
    , getValue
    )
import qualified Data.Map as Map
import qualified Data.Set as Set
#-}

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

-- | Test whether the domains of the 'UTxO' are disjoint.
disjoint : UTxO → UTxO → Bool
disjoint = Map.disjoint

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
--
-- Infix synonym: @x ⋪ utxo  =  excluding utxo x@.
--
-- Notable properties:
-- [prop-excluding-intersection](#p:prop-excluding-intersection),
-- [prop-excluding-sym](#p:prop-excluding-sym)
excluding : UTxO → Set.ℙ TxIn → UTxO
excluding = Map.withoutKeys

-- | Infix synonym for 'excluding'.
-- (Not exported to Haskell.)
_⋪_ : Set.ℙ TxIn → UTxO → UTxO
_⋪_ x u = excluding u x

-- | Restrict to a given set of inputs.
restrictedBy : UTxO → Set.ℙ TxIn → UTxO
restrictedBy = Map.restrictKeys

-- | Infix synonym for 'restrictedBy'.
-- (Not exported to Haskell.)
_⊲_ : Set.ℙ TxIn → UTxO → UTxO
_⊲_ x u = restrictedBy u x

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
{-# COMPILE AGDA2HS disjoint #-}
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
-- Two 'UTxO' are 'disjoint' if their 'dom'ains are disjoint.
--
prop-disjoint-dom
  : ∀ {ua ub : UTxO}
  → disjoint ua ub ≡ Set.disjoint (dom ua) (dom ub)
--
prop-disjoint-dom = Map.prop-disjoint-keysSet

-- |
-- The 'empty' 'UTxO' is always 'disjoint'.
prop-disjoint-empty
  : ∀ {ua : UTxO}
  → disjoint empty ua ≡ True
--
prop-disjoint-empty {ua} =
  begin
    disjoint empty ua
  ≡⟨ prop-disjoint-dom ⟩
    Set.null (Set.intersection (dom empty) (dom ua))
  ≡⟨ cong (λ o → Set.null (Set.intersection o (dom ua))) Map.prop-keysSet-empty ⟩
    Set.null (Set.intersection Set.empty (dom ua))
  ≡⟨ cong Set.null Set.prop-intersection-empty-left ⟩
    Set.null {TxIn} Set.empty
  ≡⟨ Set.prop-null-empty ⟩
    True
  ∎

-- |
-- 'empty' is a left identity of 'union'.
--
prop-union-empty-left
  : ∀ {utxo : UTxO}
  → empty ∪ utxo ≡ utxo
--
prop-union-empty-left = Map.prop-union-empty-left

-- |
-- 'empty' is a right identity of 'union'.
--
prop-union-empty-right
  : ∀ {utxo : UTxO}
  → utxo ∪ empty ≡ utxo
--
prop-union-empty-right = Map.prop-union-empty-right

-- |
-- 'union' is associative.
--
prop-union-assoc
  : ∀ {ua ub uc : UTxO}
  → (ua ∪ ub) ∪ uc ≡ ua ∪ (ub ∪ uc)
--
prop-union-assoc = Map.prop-union-assoc

-- |
-- 'union' is symmetric /if/ the 'UTxO' are disjoint.
--
prop-union-sym
  : ∀ {ua ub : UTxO}
  → disjoint ua ub ≡ True
  → ua ∪ ub ≡ ub ∪ ua
--
prop-union-sym = Map.prop-union-sym

-- |
-- Excluding the empty set does nothing.
--
@0 prop-excluding-empty
  : ∀ (utxo : UTxO)
  → excluding utxo Set.empty ≡ utxo
--
prop-excluding-empty utxo =
  Map.prop-withoutKeys-empty utxo

-- |
-- Excluding the entire domain gives the empty 'UTxO'.
--
prop-excluding-dom
  : ∀ {utxo : UTxO}
  → dom utxo ⋪ utxo ≡ empty
--
prop-excluding-dom {utxo} =
  Map.prop-withoutKeys-keysSet utxo

-- |
-- Excluding from a union is the same as excluding
-- from each member of the union.
--
prop-excluding-union
  : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
  → x ⋪ (ua ∪ ub) ≡ (x ⋪ ua) ∪ (x ⋪ ub)
--
prop-excluding-union {x} {ua} {ub} =
  Map.prop-withoutKeys-union ua ub x

-- |
-- Excluding from an exclusion is the same as excluding the union.
--
prop-excluding-excluding
  : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
  → x ⋪ (y ⋪ utxo) ≡ (Set.union x y) ⋪ utxo
--
prop-excluding-excluding {x} {y} {utxo} =
  begin
    x ⋪ (y ⋪ utxo)
  ≡⟨ Map.prop-withoutKeys-withoutKeys utxo y x ⟩
    (Set.union y x) ⋪ utxo
  ≡⟨ cong (λ o → o ⋪ utxo) Set.prop-union-sym ⟩
    (Set.union x y) ⋪ utxo
  ∎

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
-- Taking the union of a 'UTxO' with one of its exclusions
-- does nothing.
--
@0 prop-excluding-absorb
  : ∀ {x : Set.ℙ TxIn} {utxo : UTxO}
  → (x ⋪ utxo) ∪ utxo ≡ utxo
--
prop-excluding-absorb {x} {utxo} =
  begin
    (x ⋪ utxo) ∪ utxo
  ≡⟨ sym (cong (λ o → (x ⋪ utxo) ∪ o) (prop-excluding-empty utxo)) ⟩
    (x ⋪ utxo) ∪ (Set.empty ⋪ utxo)
  ≡⟨ sym prop-excluding-intersection ⟩
    (Set.intersection x Set.empty) ⋪ utxo
  ≡⟨ cong (λ o → o ⋪ utxo) Set.prop-intersection-empty-right ⟩
    Set.empty ⋪ utxo
  ≡⟨ prop-excluding-empty utxo ⟩
    utxo
  ∎

-- |
-- Excluding the difference is the same as excluding
-- everything and putting back the difference.
--
prop-excluding-difference
  : ∀ {x y : Set.ℙ TxIn} {utxo : UTxO}
  → (Set.difference x y) ⋪ utxo
    ≡ (x ⋪ utxo) ∪ (restrictedBy utxo y)
--
prop-excluding-difference {x} {y} {utxo} =
  Map.prop-withoutKeys-difference utxo x y

-- |
-- Restricting to the entire domain does nothing.
--
prop-restrictedBy-dom
  : ∀ {utxo : UTxO}
  → restrictedBy utxo (dom utxo) ≡ utxo
--
prop-restrictedBy-dom {u} = Map.prop-restrictKeys-keysSet u

-- |
-- Restricting to a set that has nothing common in common
-- will give the empty 'UTxO'.
--
prop-restrictedBy-disjoint
  : ∀ {x : Set.ℙ TxIn} {utxo : UTxO} 
  → Set.disjoint x (dom utxo) ≡ True
  → restrictedBy utxo x ≡ empty
--
prop-restrictedBy-disjoint {x} {utxo} cond =
    Map.prop-null→empty utxo1 (Map.prop-lookup-null utxo1 lem2)
  where
    utxo1 = Map.restrictKeys utxo x
    cond1 = Set.prop-null→empty {TxIn} _ cond

    lem1
      : ∀ (key : TxIn)
      → Set.member key (Set.intersection x (dom utxo)) ≡ Set.member key Set.empty
      → (Set.member key x && isJust (Map.lookup key utxo)) ≡ False
    lem1 key
      rewrite Set.prop-member-intersection key x (dom utxo)
      rewrite Map.prop-member-keysSet {TxIn} {TxOut} {key} {utxo}
      rewrite Set.prop-member-empty key
      with Set.member key x
      with Map.lookup key utxo
    ... | True  | Nothing = λ eq → refl
    ... | True  | Just a  = λ ()
    ... | False | Nothing = λ eq → refl
    ... | False | Just a  = λ eq → refl

    lem2
      : ∀ (key : TxIn)
      → Map.lookup key (Map.restrictKeys utxo x) ≡ Nothing
    lem2 key
      rewrite Map.prop-lookup-restrictKeys key utxo x
      with Set.member key x
      with Map.lookup key utxo
      with lem1 key (cong (Set.member key) cond1)
    ... | True  | Nothing | eq = refl
    ... | False | t       | eq = refl

-- |
-- Restricting a union is the same as restricting
-- from each member of the union.
--
prop-restrictedBy-union
  : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
  → x ⊲ (ua ∪ ub) ≡ (x ⊲ ua) ∪ (x ⊲ ub)
--
prop-restrictedBy-union {x} {ua} {ub} =
  Map.prop-restrictKeys-union ua ub x

-- |
-- Since 'union' is left-biased,
-- taking the union with a 'UTxO' whose domain is a subset
-- does nothing.
--
prop-union-restrictedBy-absorbs
  : ∀ {ua ub : UTxO}
  → ua ∪ (dom ua ⊲ ub) ≡ ua
--
prop-union-restrictedBy-absorbs {ua} {ub} =
  Map.prop-union-restrictKeys-absorbs ua ub

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

-- | Specification of 'excludingS':
-- Set difference with the domain of the 'UTxO'.
prop-excludingS
  : ∀ {x : Set.ℙ TxIn} {utxo : UTxO}
  → excludingS x utxo
    ≡ Set.difference x (dom utxo)
--
prop-excludingS {x} {utxo} = Set.prop-equality eq-member
  where
    p = not ∘ (λ txin → Map.member txin utxo)

    eq-member
      : ∀ (z : TxIn)
      → Set.member z (excludingS x utxo)
        ≡ Set.member z (Set.difference x (dom utxo))
    eq-member z
      rewrite Set.prop-member-filter z p x
      rewrite Set.prop-member-difference z x (dom utxo)
      rewrite sym (Map.prop-member-keysSet {TxIn} {TxOut} {z} {utxo})
      with Set.member z x
      with Set.member z (dom utxo)
    ... | True  | True = refl
    ... | True  | False = refl
    ... | False | True = refl
    ... | False | False = refl

-- |
-- Not excluding inputs makes no difference if these
-- inputs have nothing in common with the 'UTxO'.
--
prop-excluding-excludingS
  : ∀ {x : Set.ℙ TxIn} {ua ub : UTxO}
  → disjoint ua ub ≡ True
  → (excludingS x ua) ⋪ ub ≡ x ⋪ ub
--
prop-excluding-excludingS {x} {ua} {ub} cond =
  begin
    ((excludingS x ua) ⋪ ub)
  ≡⟨ cong (λ o → o ⋪ ub) prop-excludingS ⟩
    ((Set.difference x (dom ua)) ⋪ ub)
  ≡⟨ prop-excluding-difference ⟩
    ((x ⋪ ub) ∪ restrictedBy ub (dom ua))
  ≡⟨ cong (λ o → (x ⋪ ub) ∪ o) (prop-restrictedBy-disjoint {dom ua} {ub} lem1) ⟩
    (x ⋪ ub) ∪ empty
  ≡⟨ prop-union-empty-right {x ⋪ ub} ⟩
    (x ⋪ ub)
  ∎
 where
  lem1 =
    begin
      Set.disjoint (dom ua) (dom ub)
    ≡⟨ sym prop-disjoint-dom ⟩
      disjoint ua ub
    ≡⟨ cond ⟩
      True
    ∎

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
