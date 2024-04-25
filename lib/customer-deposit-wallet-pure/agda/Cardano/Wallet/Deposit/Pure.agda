{-# OPTIONS --erasure #-}

-- Experimental wallet implementation
-- with proofs for the specification.
module Cardano.Wallet.Deposit.Pure
    {-
    ; ValueTransfer
      ; TxSummary
    ; WalletState
      ; listCustomers
      ; isOurs
      ; knownCustomerAddress

      ; createAddress
      ; prop-create-derive
      ; prop-create-known

      ; availableBalance
      ; applyTx

      ; getCustomerHistory

      ; createPayment
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Pure.Address
    ( Customer
    , AddressState
    )
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO
    ( UTxO
    )
import Cardano.Wallet.Deposit.Pure.TxSummary
    ( TxSummary
    )
import qualified Cardano.Wallet.Deposit.Pure.Address as Addr
import qualified Cardano.Wallet.Deposit.Pure.UTxO.Balance as Balance
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
#-}

open import Cardano.Wallet.Deposit.Pure.Address using
    ( Customer
    ; deriveCustomerAddress
    ; AddressState
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( ValueTransfer
      ; fromSpent
      ; fromReceived
    )
open import Cardano.Wallet.Deposit.Pure.TxSummary using
    ( TxSummary
      ; mkTxSummary
    )
open import Cardano.Wallet.Deposit.Read using
    ( Address
    ; Block
    ; ChainPoint
      ; chainPointFromBlock
    ; Slot
    ; Tx
    ; TxBody
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
      ; PartialTxC
    ; balanceTransaction
    ; prop-balanceTransaction-addresses
    )
open import Haskell.Data.List.Prop using
    ( _∈_ )
open import Haskell.Data.Maybe using
    ( isJust
    ; catMaybes
    )

import Cardano.Wallet.Deposit.Pure.Address as Addr
import Cardano.Wallet.Deposit.Pure.UTxO.Balance as Balance
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Haskell.Data.Map as Map

-- The import of the cong! tactic slows down type checking…
open import Tactic.Cong using (cong!)

{-----------------------------------------------------------------------------
    Type definition
------------------------------------------------------------------------------}

record WalletState : Set where
  field
    addresses : AddressState

    utxo        : UTxO
    txSummaries : Map.Map Customer (List TxSummary)

    -- The 'localTip' is the point on the blockchain up to (and including)
    -- which the 'WalletState' has incorporated the necessary information.
    localTip    : ChainPoint

open WalletState public

{-# COMPILE AGDA2HS WalletState #-}

{-----------------------------------------------------------------------------
    Mapping between Customers and Address
------------------------------------------------------------------------------}
-- Operations

-- Specification
listCustomers : WalletState → List (Customer × Address)
listCustomers = Addr.listCustomers ∘ addresses

-- Specification
createAddress : Customer → WalletState → (Address × WalletState)
createAddress c s0 = ( addr , s1 )
  where
    pair : Address × AddressState
    pair = Addr.createAddress c (addresses s0)

    a1 = snd pair
    addr = fst pair

    s1 : WalletState
    s1 = record
      { addresses = a1
      ; utxo = utxo s0
      ; txSummaries = txSummaries s0
      ; localTip = localTip s0
      }

isOurs : WalletState → Address → Bool
isOurs s = Addr.isOurs (addresses s)

-- Properties

-- Specification
knownCustomerAddress : Address → WalletState → Bool
knownCustomerAddress address =
    elem address ∘ map snd ∘ listCustomers

--
@0 prop-create-known
  : ∀ (c  : Customer)
      (s0 : WalletState)
  → let (address , s1) = createAddress c s0
    in  knownCustomerAddress address s1 ≡ True
--
prop-create-known c s0 =
  Addr.prop-create-known c (addresses s0)

{-# COMPILE AGDA2HS listCustomers #-}
{-# COMPILE AGDA2HS createAddress #-}
{-# COMPILE AGDA2HS isOurs #-}
{-# COMPILE AGDA2HS knownCustomerAddress #-}

{-----------------------------------------------------------------------------
    Address derivation
------------------------------------------------------------------------------}

-- Specification
--
prop-create-derive
  : ∀ (c : Customer)
      (s0 : WalletState)
  → let (address , _) = createAddress c s0
    in  deriveCustomerAddress c ≡ address
--
prop-create-derive c s0 = Addr.prop-create-derive c (addresses s0)
 
{-----------------------------------------------------------------------------
    Change address generation
------------------------------------------------------------------------------}

newChangeAddress : WalletState → ChangeAddressGen ⊤
newChangeAddress = Addr.newChangeAddress ∘ addresses

--
@0 prop-changeAddress-not-Customer
  : ∀ (s : WalletState)
      (addr : Address)
  → knownCustomerAddress addr s ≡ True
  → ¬(isChange (newChangeAddress s) addr)
--
prop-changeAddress-not-Customer s addr =
  Addr.prop-changeAddress-not-Customer (addresses s) addr

{-# COMPILE AGDA2HS newChangeAddress #-}

{-----------------------------------------------------------------------------
    Tracking incoming funds
------------------------------------------------------------------------------}

isOurTxOut : WalletState → TxOut → Bool
isOurTxOut s = isOurs s ∘ TxOut.address

lookupTxIn : WalletState → TxIn → Maybe TxOut
lookupTxIn s txin = Map.lookup txin (utxo s)

relevantOutputs : WalletState → Tx → List TxOut
relevantOutputs s = filter (isOurTxOut s) ∘ TxBody.outputs ∘ Tx.txbody

relevantInputs : WalletState → Tx → List TxOut
relevantInputs s =
    catMaybes ∘ map (lookupTxIn s) ∘ TxBody.inputs ∘ Tx.txbody

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
    Map.unionWith (_<>_) ins outs
  where
    ins  = Map.map fromSpent $ summarizeInputs s tx
    outs = Map.map fromReceived $ summarizeOutputs s tx

getAddressSummary
  : Address → List (Address × TxSummary) → List TxSummary
getAddressSummary address =
  map snd ∘ filter (λ x → fst x == address)

-- Specification
getCustomerHistory : WalletState → Customer → List TxSummary
getCustomerHistory s c = concat (Map.lookup c (txSummaries s))

{-# COMPILE AGDA2HS getCustomerHistory #-}

{-
--
prop-txout-only-isOurs
  : ∀ (address : Address)
      (s : WalletState)
      (tx : Tx)
  → Map.member address (summarizeOutputs s tx) ≡ True
  → isOurs s address ≡ True
--
prop-txout-only-isOurs address s tx eq = {!   !}
  where
    lem1 : _
    lem1 =
      begin
        Map.member address (summarizeOutputs s tx)
      ≡⟨⟩
        elem address ((map fst ∘ map pairFromTxOut ∘ relevantOutputs s) tx)
      ≡⟨⟩
        elem address ((map TxOut.address ∘ relevantOutputs s) tx)
      ≡⟨⟩
        elem address ((map TxOut.address ∘ relevantOutputs s) tx)
      ∎

    lem2 : elem y ∘ map f xs ≡ ∃ (λ x → (y ≡ f x && elem x xs ≡ True))
    lem2 = ?

    lem2 : (elem x ∘ filter p) xs ≡ p x && elem x xs
    lem2 = ?

--
prop-track-only-isOurs
  : ∀ (address : Address)
      (s : WalletState)
      (tx : Tx)
  → Map.member address (summarizeTx s tx) ≡ True
  → isOurs s address ≡ True
--
prop-track-only-isOurs address s tx eq = {!   !}
-}

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

-}


{-----------------------------------------------------------------------------
    Applying transactions
------------------------------------------------------------------------------}

-- Specification
availableBalance : WalletState → Value
availableBalance = UTxO.balance ∘ utxo

{-# COMPILE AGDA2HS availableBalance #-}

-- Specification
applyTx : Tx → WalletState → WalletState
applyTx tx s0 = s1
  where
    s1 : WalletState
    s1 = record
      { addresses = addresses s0
      ; utxo = snd (Balance.applyTx (isOurs s0) tx (utxo s0))
      ; txSummaries = txSummaries s0
      ; localTip = localTip s0
      }

{-# COMPILE AGDA2HS applyTx #-}

-- | Roll the 'WalletState' forward by one block.
rollForwardOne : Block → WalletState → WalletState
rollForwardOne block s0 =
    record s1 { localTip = chainPointFromBlock block }
  where
    s1 = foldl (λ s tx → applyTx tx s) s0 (Block.transactions block)

{-# COMPILE AGDA2HS rollForwardOne #-}

{-----------------------------------------------------------------------------
    Creating transactions
------------------------------------------------------------------------------}

txOutFromPair : Address × Value → TxOut
txOutFromPair (x , y) = record { address = x ; value = y }

-- Specification
createPayment
    : List (Address × Value)
    → WalletState
    → Maybe TxBody
createPayment destinations s =
    balanceTransaction (utxo s) (newChangeAddress s) tt partialTx
  where
    partialTx = PartialTxC (map txOutFromPair destinations)

maxFee : Value
maxFee = mempty

{-# COMPILE AGDA2HS txOutFromPair #-}
{-# COMPILE AGDA2HS createPayment #-}

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
    Proposition: Never sends funds to known address
------------------------------------------------------------------------------}

lemma-neg-or
  : ∀ {A B : Set}
  → (A ⋁ B) → (¬ B) → A
lemma-neg-or (inl a) _ = a
lemma-neg-or (inr b) ¬b = magic (¬b b)

lemma-neg-impl
  : ∀ {A B : Set}
  → (A → B) → ¬ B → ¬ A
lemma-neg-impl = λ f ¬b a → ¬b (f a)

--
@0 prop-createPayment-not-known
  : ∀ (s : WalletState)
      (destinations : List (Address × Value))
      (tx : TxBody)
  → createPayment destinations s ≡ Just tx
  → ∀ (address : Address)
    → knownCustomerAddress address s ≡ True
    → ¬ (address ∈ map fst destinations)
    → ¬ (address ∈ map TxOut.address (TxBody.outputs tx))
--
prop-createPayment-not-known s destinations tx created addr known ¬dest =
    lemma-neg-impl
        (λ outs → lemma-neg-or (changeOrPartial outs) lem2)
        (prop-changeAddress-not-Customer s addr known)
  where
    new = newChangeAddress s
    partialTx = record { outputs = map txOutFromPair destinations }

    lem1 =
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
    
    lem2 : ¬(addr ∈ map TxOut.address (PartialTx.outputs partialTx))
    lem2 p rewrite lem1 = ¬dest p

    changeOrPartial
      : addr ∈ map TxOut.address (TxBody.outputs tx)
      → isChange new addr
        ⋁ addr ∈ map TxOut.address (PartialTx.outputs partialTx)
    changeOrPartial =
      prop-balanceTransaction-addresses
        (utxo s) partialTx (newChangeAddress s) tt tx created addr

 