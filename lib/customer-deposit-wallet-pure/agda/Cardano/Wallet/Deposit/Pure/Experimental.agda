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
      ; fromNetworkId
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
      ; slotFromChainPoint
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
open import Haskell.Data.Word.Odd using
    ( Word31
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

defaultNetworkId : NetworkId
defaultNetworkId = NetworkId.Mainnet

getNetworkTag : WalletState → NetworkTag
getNetworkTag s = Addr.getNetworkTag (addresses s)

{-# COMPILE AGDA2HS getXPub #-}
{-# COMPILE AGDA2HS defaultNetworkId #-}
{-# COMPILE AGDA2HS getNetworkTag #-}

{-----------------------------------------------------------------------------
    Mapping between Customers and Addresses
------------------------------------------------------------------------------}
-- Operations

-- Specification
deriveCustomerAddress : XPub → Customer → Address
deriveCustomerAddress =
    Addr.deriveCustomerAddress (fromNetworkId defaultNetworkId)

-- Specification
fromXPubAndMax : XPub → Word31 → WalletState
fromXPubAndMax xpub cmax = record
    { addresses = Addr.fromXPubAndMax defaultNetworkId xpub cmax 
    ; utxo = UTxO.empty
    ; txSummaries = Map.empty
    ; localTip = ChainPoint.GenesisPoint
    }

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

-- Specification
knownCustomerAddress : Address → WalletState → Bool
knownCustomerAddress a =
    elem a ∘ map snd ∘ listCustomers

-- Specification
isOurs : WalletState → Address → Bool
isOurs s = Addr.isOurs (addresses s)

{-# COMPILE AGDA2HS deriveCustomerAddress #-}
{-# COMPILE AGDA2HS fromXPubAndMax #-}
{-# COMPILE AGDA2HS listCustomers #-}
{-# COMPILE AGDA2HS isOurs #-}
{-# COMPILE AGDA2HS knownCustomerAddress #-}

{-----------------------------------------------------------------------------
    Transactions and slots
------------------------------------------------------------------------------}

-- Specification
getWalletSlot : WalletState → Slot
getWalletSlot = slotFromChainPoint ∘ localTip

-- Specification
applyTx
  : ∀{era} → {{IsEra era}}
  → Slot → Tx era → WalletState → WalletState
applyTx slot tx s0 = s1
  where
    s1 : WalletState
    s1 = record
      { addresses = addresses s0
      ; utxo = snd (UTxO.applyTx (isOurs s0) tx (utxo s0))
      ; txSummaries = txSummaries s0
      ; localTip = localTip s0
      -- FIXME! `applyTx` needs a chainpoint as argument.
      }

{-# COMPILE AGDA2HS getWalletSlot #-}
{-# COMPILE AGDA2HS applyTx #-}

-- | Roll the 'WalletState' forward by one block.
rollForwardOne
  : ∀ {era} → {{IsEra era}} → Block era → WalletState → WalletState
rollForwardOne block s0 =
    record s1 { localTip = getChainPoint block }
  where
    slot = slotFromChainPoint (getChainPoint block)
    s1 = foldl (λ s tx → applyTx slot tx s) s0 (getEraTransactions block)

{-# COMPILE AGDA2HS rollForwardOne #-}

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

{-----------------------------------------------------------------------------
    Wallet balance and transactions
------------------------------------------------------------------------------}

-- Specification
totalUTxO : WalletState → UTxO
totalUTxO = utxo

{-# COMPILE AGDA2HS totalUTxO #-}

{-----------------------------------------------------------------------------
    Creating transactions
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
