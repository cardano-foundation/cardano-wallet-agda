{-# OPTIONS --erasure #-}

-- Experimental wallet implementation
-- with proofs for the specification.
module Cardano.Wallet.Deposit.Pure.Experimental
    {-
    ; ValueTransfer
      ; TxSummary
    ; WalletState
      ; getXPub

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
-- Working around a limitation in agda2hs regarding re-exports
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
import qualified Cardano.Wallet.Deposit.Pure.UTxO.Tx as UTxO
import qualified Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
#-}

open import Cardano.Wallet.Address.BIP32_Ed25519 using
    ( XPub
    )
open import Cardano.Wallet.Address.Encoding using
    ( NetworkTag
    )
open import Cardano.Wallet.Deposit.Pure.Address public using
    ( deriveCustomerAddress
    )
open import Cardano.Wallet.Deposit.Pure.Address using
    ( Customer
    ; AddressState
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.UTxO using
    ( UTxO
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer public using
    ( ValueTransfer
    )
open import Cardano.Wallet.Deposit.Pure.UTxO.ValueTransfer using
    ( fromSpent
    ; fromReceived
    )
open import Cardano.Wallet.Deposit.Pure.TxSummary public using
    ( TxSummary
    )
open import Cardano.Wallet.Deposit.Pure.TxSummary using
    ( mkTxSummary
    )
open import Cardano.Wallet.Deposit.Read.Temp using
    ( Address
    ; TxBody
    )
open import Cardano.Wallet.Read using
    ( Block
      ; getEraTransactions
    ; ChainPoint
      ; getChainPoint
    ; IsEra
    ; NetworkId
    ; Slot
    ; Tx
    ; TxId
    ; TxIn
    ; TxOut
      ; getCompactAddr
      ; getValue
      ; mkBasicTxOut
      ; prop-getCompactAddr-mkBasicTxOut
    ; Value
      ; largerOrEqual
      ; iEqValue
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
import Cardano.Wallet.Deposit.Pure.UTxO.Tx as UTxO
import Cardano.Wallet.Deposit.Pure.UTxO.UTxO as UTxO
import Data.Map as Map

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

getXPub : WalletState → XPub
getXPub = Addr.getXPub ∘ addresses

getNetworkTag : WalletState → NetworkTag
getNetworkTag s = Addr.getNetworkTag (addresses s)

{-# COMPILE AGDA2HS getXPub #-}
{-# COMPILE AGDA2HS getNetworkTag #-}

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
    in  deriveCustomerAddress (getNetworkTag s0) (getXPub s0) c ≡ address
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

summarizeTx
  : ∀ {era} → {{IsEra era}}
  → WalletState → Tx era → Map.Map Address ValueTransfer
summarizeTx s tx =
    UTxO.valueTransferFromDeltaUTxO (utxo s) du
  where
    du = fst (UTxO.applyTx (isOurs s) tx (utxo s))

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
applyTx : ∀{era} → {{IsEra era}} → Tx era → WalletState → WalletState
applyTx tx s0 = s1
  where
    s1 : WalletState
    s1 = record
      { addresses = addresses s0
      ; utxo = snd (UTxO.applyTx (isOurs s0) tx (utxo s0))
      ; txSummaries = txSummaries s0
      ; localTip = localTip s0
      }

{-# COMPILE AGDA2HS applyTx #-}

-- | Roll the 'WalletState' forward by one block.
rollForwardOne
  : ∀ {era} → {{IsEra era}} → Block era → WalletState → WalletState
rollForwardOne block s0 =
    record s1 { localTip = getChainPoint block }
  where
    s1 = foldl (λ s tx → applyTx tx s) s0 (getEraTransactions block)

{-# COMPILE AGDA2HS rollForwardOne #-}

{-----------------------------------------------------------------------------
    Creating transactions
------------------------------------------------------------------------------}

txOutFromPair : Address × Value → TxOut
txOutFromPair (x , y) = mkBasicTxOut x y

prop-getCompactAddr-txOutFromPair
  : (getCompactAddr ∘ txOutFromPair) ≡ fst
prop-getCompactAddr-txOutFromPair =
  ext (λ { (x , y) → prop-getCompactAddr-mkBasicTxOut x y })

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
    → largerOrEqual (availableBalance s) (totalValue destinations <> maxFee) ≡ True
    → isJust (createPayment destinations s) ≡ True
prop-createPayment-success = λ s destinations x → {!   !}
-}

{-----------------------------------------------------------------------------
    Creating transactions
    Proposition: Never sends funds to known address
------------------------------------------------------------------------------}

--
@0 prop-createPayment-not-known
  : ∀ (s : WalletState)
      (destinations : List (Address × Value))
      (tx : TxBody)
  → createPayment destinations s ≡ Just tx
  → ∀ (address : Address)
    → knownCustomerAddress address s ≡ True
    → ¬ (address ∈ map fst destinations)
    → ¬ (address ∈ map getCompactAddr (TxBody.outputs tx))
--
prop-createPayment-not-known s destinations tx created addr known ¬dest =
  λ outs →
    case changeOrPartial outs of λ
      { (inl caseChange) →
          magic (prop-changeAddress-not-Customer s addr known caseChange)
      ; (inr casePartial) →
          magic (lem2 casePartial)
      }
  where
    new = newChangeAddress s
    partialTx = record { outputs = map txOutFromPair destinations }

    lem1 =
      begin
        map getCompactAddr (PartialTx.outputs partialTx)
      ≡⟨⟩
        map getCompactAddr (map txOutFromPair destinations)
      ≡⟨ sym (map-∘ _ _ destinations) ⟩
        map (getCompactAddr ∘ txOutFromPair) destinations
      ≡⟨⟩
        map (λ x → getCompactAddr (txOutFromPair x)) destinations
      ≡⟨ cong (λ f → map f destinations) prop-getCompactAddr-txOutFromPair ⟩
        map (λ x → fst x) destinations
      ∎
    
    lem2 : ¬(addr ∈ map getCompactAddr (PartialTx.outputs partialTx))
    lem2 p rewrite lem1 = ¬dest p

    changeOrPartial
      : addr ∈ map getCompactAddr (TxBody.outputs tx)
      → isChange new addr
        ⋁ addr ∈ map getCompactAddr (PartialTx.outputs partialTx)
    changeOrPartial =
      prop-balanceTransaction-addresses
        (utxo s) partialTx (newChangeAddress s) tt tx created addr

 