{-# OPTIONS --erasure #-}

-- Experimental wallet implementation
-- with proofs for the specification.
module Cardano.Wallet.Deposit.Pure
    {-
    ; ValueTransfer
      ; TxSummary
    ; WalletState
      ; listCustomers
      ; createAddress

      ; availableBalance
      ; applyTx

      ; getCustomerHistory

      ; createPayment
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Deposit.Pure.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; Slot
    ; Tx
    ; TxId
    ; TxIn
    ; TxOut
    ; Value
    ; exceeds
    )
open import Cardano.Write.Tx.Balance using
    ( ChangeAddressGen
    ; isChange
    ; PartialTx
    ; balanceTransaction
    ; prop-balanceTransaction-addresses
    )
open import Haskell.Data.List.Prop using
    ( _∈_ )
open import Haskell.Data.Maybe using
    ( isJust
    ; catMaybes
    )

import Cardano.Wallet.Deposit.Pure.Balance as Balance
import Cardano.Wallet.Deposit.Pure.UTxO as UTxO
import Haskell.Data.Map as Map

-- The import of the cong! tactic slows down type checking…
open import Tactic.Cong using (cong!)

{-----------------------------------------------------------------------------
    Assumptions
------------------------------------------------------------------------------}

record ValueTransfer : Set where
  field
    spent    : Value
    received : Value

open ValueTransfer

TxSummary : Set
TxSummary = Slot × TxId × ValueTransfer

{-----------------------------------------------------------------------------
    Type definition
------------------------------------------------------------------------------}

Customer = Nat

record WalletState : Set where
  field
    addresses : Map.Map Address Customer
    change    : Address

    utxo        : UTxO
    txSummaries : Map.Map Customer (List TxSummary)

open WalletState

{-----------------------------------------------------------------------------
    Mapping between Customers and Address
------------------------------------------------------------------------------}
-- Operations

-- Helper function
swap : ∀ {a b : Set} → a × b → b × a
swap (x , y) = (y , x)

-- Specification
listCustomers : WalletState → List (Customer × Address)
listCustomers = map swap ∘ Map.toAscList ∘ addresses

deriveAddress : Nat → Address
deriveAddress ix = suc ix

-- Specification
createAddress : Customer → WalletState → (Address × WalletState)
createAddress c s0 = ( addr , s1 )
  where
    addr = deriveAddress c

    s1 : WalletState
    addresses s1 = Map.insert addr c (addresses s0)
    change s1 = change s0
    utxo s1 = utxo s0
    txSummaries s1 = txSummaries s0

isCustomerAddress : WalletState → Address → Bool
isCustomerAddress = λ s addr → isJust $ Map.lookup addr (addresses s)

isChangeAddress : WalletState → Address → Bool
isChangeAddress = λ s addr → change s == addr

isOurs : WalletState → Address → Bool
isOurs = λ s addr → isChangeAddress s addr || isCustomerAddress s addr

-- Properties

-- Specification
knownCustomerAddress : Address → WalletState → Bool
knownCustomerAddress address = elem address ∘ map snd ∘ listCustomers

-- alternate definition of knownCustomerAddress
knownCustomerAddress' : Address → WalletState → Bool
knownCustomerAddress' address =
    elem address ∘ map fst ∘ Map.toAscList ∘ addresses

-- alternate definition and original definition are equal
lemma-known-known'
  : ∀ (a : Address) (s : WalletState)
  → knownCustomerAddress a s ≡ knownCustomerAddress' a s
lemma-known-known' a s =
  begin
    (elem a ∘ map snd ∘ listCustomers) s
  ≡⟨⟩
    (elem a ∘ map snd ∘ map swap ∘ Map.toAscList ∘ addresses) s
  ≡⟨ cong (elem a) (sym (map-∘ snd swap (Map.toAscList (addresses s)))) ⟩
    (elem a ∘ map (snd ∘ swap) ∘ Map.toAscList ∘ addresses) s
  ≡⟨⟩
    (elem a ∘ map fst ∘ Map.toAscList ∘ addresses) s
  ∎

-- lemma about converting == to ≡
lemma-lookup-insert-same
    : ∀ (a : Address) (c : Customer) (m : Map.Map Address Customer)
    → Map.lookup a (Map.insert a c m) ≡ Just c
lemma-lookup-insert-same a c m =
  begin
    Map.lookup a (Map.insert a c m)
  ≡⟨ Map.prop-lookup-insert a a c m ⟩
    (if (a == a) then Just c else Map.lookup a m)
  ≡⟨ cong! (equality' a a refl) ⟩
    (if True then Just c else Map.lookup a m)
  ≡⟨⟩
    Just c
  ∎

-- Specification
prop-create-known
  : ∀ (c : Customer) (s0 : WalletState)
  → let (address , s1) = createAddress c s0
    in  knownCustomerAddress address s1 ≡ True
prop-create-known c s0 =
  let (a , s1) = createAddress c s0
  in
    begin
      knownCustomerAddress a s1
    ≡⟨ lemma-known-known' a s1 ⟩
      knownCustomerAddress' a s1
    ≡⟨ Map.prop-lookup-toAscList-Just a c (addresses s1)
        (lemma-lookup-insert-same a c (addresses s0))
      ⟩
      True
    ∎

{-----------------------------------------------------------------------------
    Address derivation
------------------------------------------------------------------------------}

-- Specification
prop-create-derive
  : ∀ (c : Customer) (s0 : WalletState)
  → let (address , _) = createAddress c s0
    in  deriveAddress c ≡ address
prop-create-derive = λ c s0 → refl
 
{-----------------------------------------------------------------------------
    Tracking incoming funds
------------------------------------------------------------------------------}

fromSpent : Value → ValueTransfer
fromSpent = λ value → record { spent = value ; received = mempty }

fromReceived : Value → ValueTransfer
fromReceived = λ value → record { spent = mempty ; received = value }

combine : ValueTransfer → ValueTransfer → ValueTransfer
combine = λ v1 v2 → record
    { spent = spent v1 <> spent v2
    ; received = received v1 <> received v2
    }

isOurTxOut : WalletState → TxOut → Bool
isOurTxOut s = isOurs s ∘ TxOut.address

lookupTxIn : WalletState → TxIn → Maybe TxOut
lookupTxIn s txin = Map.lookup txin (utxo s)

relevantOutputs : WalletState → Tx → List TxOut
relevantOutputs s = filter (isOurTxOut s) ∘ Tx.outputs

relevantInputs : WalletState → Tx → List TxOut
relevantInputs s =
    catMaybes ∘ map (lookupTxIn s) ∘ Tx.inputs

pairFromTxOut : TxOut → (Address × Value)
pairFromTxOut = λ txout → (TxOut.address txout , TxOut.value txout)

summarizeInputs : WalletState → Tx → Map.Map Address Value
summarizeInputs s =
    Map.fromListWith (_<>_) ∘ map pairFromTxOut ∘ relevantInputs s

summarizeOutputs : WalletState → Tx → Map.Map Address Value
summarizeOutputs s =
    Map.fromListWith (_<>_) ∘ map pairFromTxOut ∘ relevantOutputs s

summarizeTx : WalletState → Tx → Map.Map Address ValueTransfer
summarizeTx s tx =
    Map.unionWith combine ins outs
  where
    ins  = Map.map fromSpent $ summarizeInputs s tx
    outs = Map.map fromReceived $ summarizeOutputs s tx

mkTxSummary : Tx → ValueTransfer → TxSummary
mkTxSummary = λ tx transfer → (0 , Tx.txid tx , transfer)


getAddressSummary
  : Address → List (Address × TxSummary) → List TxSummary
getAddressSummary address =
  map snd ∘ filter (λ x → fst x == address)

-- Specification
getCustomerHistory : WalletState → Customer → List TxSummary
getCustomerHistory s c = []

{-
prop_getAddressHistory-summary
  : ∀ (s : WalletState)
      (c : Customer)
      (address : Address)
      (tx : Tx)
  → (c , address) ∈ listCustomers s
  → getCustomerHistory (applyTx tx s) c
    ≡ (getAddressSummary address (summarize s tx))
        ++ getCustomerHistory s c


prop_tx-known-address
  : ∀ (address : Address)
      (s : WalletState)
      (tx : Tx)
  → (knownCustomerAddress address s ≡ True)
  ⟷ (address ∈ map fst (summarize s tx))
-}


{-----------------------------------------------------------------------------
    Applying transactions
------------------------------------------------------------------------------}

-- Specification
availableBalance : WalletState → Value
availableBalance = UTxO.balance ∘ utxo

-- Specification
applyTx : Tx → WalletState → WalletState
applyTx tx s0 = s1
  where
    s1 : WalletState
    addresses s1 = addresses s0
    change s1 = change s0
    utxo s1 = snd $ Balance.applyTx (isOurs s0) tx (utxo s0)
    txSummaries s1 = txSummaries s0


{-----------------------------------------------------------------------------
    Creating transactions
------------------------------------------------------------------------------}

txOutFromPair : Address × Value → TxOut
txOutFromPair (x , y) = record { address = x ; value = y }

newAddress : WalletState → ChangeAddressGen ⊤
newAddress s = λ _ → (change s , tt)

-- Specification
createPayment
    : List (Address × Value)
    → WalletState
    → Maybe Tx
createPayment destinations s =
    balanceTransaction (utxo s) (newAddress s) tt partialTx
  where
    partialTx = record { outputs = map txOutFromPair destinations }

maxFee : Value
maxFee = mempty

{-----------------------------------------------------------------------------
    Creating transactions
    Property: Successfully creating a transaction
------------------------------------------------------------------------------}

totalValue : List (Address × Value) → Value
totalValue = mconcat ∘ map snd

{-
prop-createPayment-success
    : ∀ (s : WalletState)
        (destinations : List (Address × Value))
    → exceeds (availableBalance s) (totalValue destinations <> maxFee) ≡ True
    → isJust (createPayment destinations s) ≡ True
prop-createPayment-success = λ s destinations x → {!   !}
-}

{-----------------------------------------------------------------------------
    Creating transactions
    Property: Never sends funds to known address
------------------------------------------------------------------------------}

lemma-address-not-known
  : ∀ (s : WalletState)
      (address : Address)
  → knownCustomerAddress address s ≡ True
  → ¬(isChange (newAddress s) address)

lemma-address-not-known = {!   !}

lemma-neg-or
  : ∀ {A B : Set}
  → (A ⋁ B) → (¬ B) → A
lemma-neg-or (inl a) _ = a
lemma-neg-or (inr b) ¬b = magic (¬b b)

lemma-neg-impl
  : ∀ {A B : Set}
  → (A → B) → ¬ B → ¬ A
lemma-neg-impl = λ f ¬b a → ¬b (f a)

prop-createPayment-not-known
  : ∀ (s : WalletState)
      (destinations : List (Address × Value))
      (tx : Tx)
  → createPayment destinations s ≡ Just tx
  → ∀ (address : Address)
    → knownCustomerAddress address s ≡ True
    → ¬ (address ∈ map fst destinations)
    → ¬ (address ∈ map TxOut.address (Tx.outputs tx))

prop-createPayment-not-known s destinations tx created addr known ¬dest =
    lemma-neg-impl
        (λ outs → lemma-neg-or (changeOrPartial outs) ¬partial)
        (lemma-address-not-known s addr known)
  where
    new = newAddress s
    partialTx = record { outputs = map txOutFromPair destinations }

    lemma1 =
      begin
        map TxOut.address (PartialTx.outputs partialTx)
      ≡⟨⟩
        map TxOut.address (map txOutFromPair destinations)
      ≡⟨ sym (map-∘ _ _ destinations) ⟩
        map (TxOut.address ∘ txOutFromPair) destinations
      ≡⟨⟩
        map (λ x → TxOut.address (txOutFromPair x)) destinations
      ≡⟨⟩
        map (λ x → fst x) destinations
      ∎
    
    ¬partial : ¬ (addr ∈ map TxOut.address (PartialTx.outputs partialTx))
    ¬partial p rewrite lemma1 = ¬dest p

    ¬change : ¬ (isChange new addr)
    ¬change = lemma-address-not-known s addr known

    changeOrPartial
      : addr ∈ map TxOut.address (Tx.outputs tx)
      → isChange new addr
        ⋁ addr ∈ map TxOut.address (PartialTx.outputs partialTx)
    changeOrPartial =
      prop-balanceTransaction-addresses
        (utxo s) partialTx (newAddress s) tt tx created addr

 