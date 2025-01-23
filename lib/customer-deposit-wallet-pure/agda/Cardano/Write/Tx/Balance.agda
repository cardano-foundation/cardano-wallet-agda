{-# OPTIONS --erasure #-}

module Cardano.Write.Tx.Balance
    {-
    ; ChangeAddressGen
        ; isChange
    ; PartialTx
        ; totalOut
    ; balanceTransaction
        ; prop-balanceTransaction-addresses
        ; prop-balanceTransaction-suceeds
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

{-# FOREIGN AGDA2HS
import Prelude hiding (subtract)
#-}

open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Read.Temp using
    ( Address
    ; TxBody
    )
open import Cardano.Wallet.Read using
    ( TxIn
    ; TxOut
      ; getCompactAddr
      ; getValue
      ; mkBasicTxOut
      ; prop-getCompactAddr-mkBasicTxOut
    ; Value
    ; largerOrEqual
    ; subtract
    )
open import Haskell.Data.List.Prop using ( _∈_ )
open import Haskell.Data.Maybe using ( isJust )

import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Haskell.Data.ByteString as BS
import Haskell.Data.Map as Map

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read
    ( TxIn
    , TxOut
    , Value
    , getCompactAddr
    , getValue
    , mkBasicTxOut
    , largerOrEqual
    , subtract
    )
import qualified Data.ByteString as BS
import qualified Data.Map as Map
#-}

{-----------------------------------------------------------------------------
    Partial transactions
------------------------------------------------------------------------------}

-- | Partially constructed 'Tx'.
--
-- NOTE: Currently mostly a mock type.
record PartialTx : Set where
  constructor PartialTxC
  field
    outputs : List TxOut

open PartialTx public

-- | Total output 'Value' of a partially constructed transaction.
totalOut : PartialTx → Value
totalOut = mconcat ∘ map getValue ∘ PartialTx.outputs

{-# COMPILE AGDA2HS PartialTx #-}
{-# COMPILE AGDA2HS totalOut #-}

{-----------------------------------------------------------------------------
    Change addresses
------------------------------------------------------------------------------}

-- | Represents a function that creates a fresh
-- change address from a state @c@.
ChangeAddressGen : Set → Set
ChangeAddressGen c = c → (Address × c)

isChange : ChangeAddressGen c → Address → Set
isChange = λ gen addr → ∃ (λ c → fst (gen c) ≡ addr)

{-# COMPILE AGDA2HS ChangeAddressGen #-}

{-----------------------------------------------------------------------------
    Coin selection
------------------------------------------------------------------------------}

-- | (Internal, exported for technical reasons.)
secondCons : ∀ {a b : Set} → b → (a × List b) → (a × List b)
secondCons y (x , ys) = (x , y ∷ ys)

-- | Greedily select inputs from a list in order to exceed a given value.
coinSelectionGreedy
    : Value → List (TxIn × TxOut) → (Value × List TxIn)
coinSelectionGreedy v [] = (mempty , [])
coinSelectionGreedy v ((txin , txout) ∷ xs) =
    let dv = getValue txout
    in  if largerOrEqual v dv
            then secondCons txin $ coinSelectionGreedy (subtract v dv) xs
            else (subtract dv v , [])

{-# COMPILE AGDA2HS secondCons #-}
{-# COMPILE AGDA2HS coinSelectionGreedy #-}

{-----------------------------------------------------------------------------
    Balance transaction
------------------------------------------------------------------------------}

-- | Balance a partial transaction by selecting inputs
-- and assigning change addresses.
balanceTransaction
    : UTxO
    → ChangeAddressGen c
    → c
    → PartialTx
    → Maybe TxBody
balanceTransaction utxo newAddress c0 partialTx =
    let (changeValue , ins) = coinSelectionGreedy target (Map.toAscList utxo)
        changeOutput =
          mkBasicTxOut (fst (newAddress c0)) changeValue
    in
    if largerOrEqual target (UTxO.balance utxo)
        then Nothing
        else Just $ record
          { outputs = changeOutput ∷ PartialTx.outputs partialTx
          ; inputs = ins
          }
  where
    target = totalOut partialTx

{-# COMPILE AGDA2HS balanceTransaction #-}

unequal : ∀ {A : Set} (x : A) → Nothing ≡ Just x → ⊥
unequal x ()

unJust : ∀ {A : Set} {x y : A} → Just x ≡ Just y → x ≡ y
unJust refl = refl

{-----------------------------------------------------------------------------
    Balance transaction
    Property: Addresses
------------------------------------------------------------------------------}

lemma-balanceTransaction-addresses
  : ∀ (u : UTxO)
      (partialTx : PartialTx)
      (new : ChangeAddressGen c)
      (c0 : c)
      (tx : TxBody)
  → balanceTransaction u new c0 partialTx ≡ Just tx 
  → map getCompactAddr (TxBody.outputs tx)
    ≡ fst (new c0) ∷ map getCompactAddr (PartialTx.outputs partialTx)
lemma-balanceTransaction-addresses u partialTx new c0 tx balance
  with largerOrEqual (totalOut partialTx) (UTxO.balance u)
...  | True = magic (unequal tx balance)
...  | False = begin
          map getCompactAddr (TxBody.outputs tx)
        ≡⟨ cong (λ x → map getCompactAddr (TxBody.outputs x)) (sym (unJust balance)) ⟩
          getCompactAddr (mkBasicTxOut (fst (new c0)) _) ∷ map getCompactAddr (PartialTx.outputs partialTx)
        ≡⟨ cong (λ x → x ∷ _) (prop-getCompactAddr-mkBasicTxOut (fst (new c0)) _) ⟩
          fst (new c0) ∷ map getCompactAddr (PartialTx.outputs partialTx)
        ∎

lemma-isChange-c0
  : ∀ (new : ChangeAddressGen c)
      (c0 : c)
      (addr : Address)
  → addr ≡ fst (new c0)
  → isChange new addr
lemma-isChange-c0 = λ new c0 addr x → c0 `witness` (sym x)

onLeft
  : ∀ {p p' q : Set} → (p → p') → p ⋁ q → p' ⋁ q
onLeft f (inl p) = inl (f p)
onLeft f (inr q) = inr q

-- | How balanceTransaction assigns addresses to outputs:
-- Each output is either
-- * a change address
-- * an address from the input partial transaction
prop-balanceTransaction-addresses
  : ∀ (u : UTxO)
      (partialTx : PartialTx)
      (new : ChangeAddressGen c)
      (c0 : c)
      (tx : TxBody)
  → balanceTransaction u new c0 partialTx ≡ Just tx
  → ∀ (addr : Address)
    → addr ∈ map getCompactAddr (TxBody.outputs tx)
    → isChange new addr
        ⋁ addr ∈ map getCompactAddr (PartialTx.outputs partialTx)
--
prop-balanceTransaction-addresses u partialTx new c0 tx balance addr el
    = onLeft lemma2 (prop-||-⋁ (sym lemma1))
  where
    lemma1 =
      begin
        True
      ≡⟨ sym el ⟩
        elem addr (map getCompactAddr $ TxBody.outputs tx)
      ≡⟨ cong (elem addr) (lemma-balanceTransaction-addresses u partialTx new c0 tx balance) ⟩
        elem addr (fst (new c0) ∷ map getCompactAddr (PartialTx.outputs partialTx))
      ≡⟨⟩
        ((addr == fst (new c0))
            || (elem addr $ map getCompactAddr $ PartialTx.outputs partialTx))
      ∎

    b1 b2 : Bool
    b1 = (addr == fst (new c0))
    b2 = (elem addr $ map getCompactAddr $ PartialTx.outputs partialTx)

    lemma2
      : (addr == fst (new c0)) ≡ True
      → isChange new addr
    lemma2 =
      lemma-isChange-c0 new c0 addr
      ∘ equality addr (fst (new c0))

{-----------------------------------------------------------------------------
    Balance transaction
    Property: Balancing success
------------------------------------------------------------------------------}

{-
prop-balanceTransaction-suceeds
    : ∀ (u : UTxO)
        (partialTx : PartialTx)
        (newAddress : ChangeAddressGen c)
        (c0 : c)
    → exceeds (UTxO.balance u) (totalOut partialTx) ≡ True
    → isJust (balanceTransaction u newAddress c0 partialTx) ≡ True
prop-balanceTransaction-suceeds = {!   !}
-}