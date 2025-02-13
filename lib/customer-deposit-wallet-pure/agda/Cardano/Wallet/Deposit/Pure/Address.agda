{-# OPTIONS --erasure #-}

-- Address management for the Customer Deposit Wallet
module Cardano.Wallet.Deposit.Pure.Address
    {-|
    -- * Deriving addresses
    ; Customer
      ; deriveCustomerAddress

    -- * AddressState
    -- ** Construction
    ; AddressState
      ; getNetworkTag
      ; getXPub
      ; emptyFromXPub
      ; fromXPubAndCount

    -- ** Address observation
      ; isCustomerAddress
        ; prop-isCustomerAddress-deriveCustomerAddress
      ; isChangeAddress
      ; isOurs
        ; prop-isOurs
        ; prop-isOurs-from-isCustomerAddress
      ; getBIP32Path
      ; listCustomers
      ; knownCustomerAddress
      ; getKnownCustomerCount

    -- ** Address creation
      ; newChangeAddress
      ; prop-changeAddress-not-Customer
      ; mockMaxLengthChangeAddress
      ; prop-isOurs-mockMaxLengthChangeAddress-False
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Cardano.Wallet.Address.BIP32 using
    ( BIP32Path
    ; DerivationType
      ; Hardened
      ; Soft
    )
open import Cardano.Wallet.Address.BIP32_Ed25519 using
    ( XPub
    ; deriveXPubSoft
    ; rawSerialiseXPub
    ; prop-deriveXPubSoft-injective
    ; prop-deriveXPubSoft-not-identity
    ; prop-rawSerialiseXPub-injective
    )
open import Cardano.Wallet.Address.Encoding using
    ( Credential
      ; credentialFromXPub
      ; prop-credentialFromXPub-injective
    ; NetworkTag
      ; fromNetworkId
    ; EnterpriseAddr
      ; EnterpriseAddrC
      ; compactAddrFromEnterpriseAddr
      ; prop-compactAddrFromEnterpriseAddr-injective
    )
open import Cardano.Wallet.Deposit.Read.Temp using
    ( Address
    )
open import Cardano.Wallet.Read using
    ( NetworkId
    )
open import Cardano.Write.Tx.Balance using
    ( ChangeAddressGen
    ; isChange
    )
open import Data.Maybe.Extra using
  ( prop-Just-injective
  )
open import Haskell.Data.List.Prop using
    ( _∈_ )
open import Haskell.Data.Maybe using
    ( isJust
    ; catMaybes
    )
open import Haskell.Data.Word using
    ( Word8
    ; word8FromNat
    )
open import Haskell.Data.Word.Odd using
    ( Word31
    ; word31FromNat
    )
open import Haskell.Data.Word public using
    ( iOrdWord8
    )
open import Haskell.Data.Word.Odd public using
    ( iOrdWord31
    )

import Haskell.Data.ByteString as BS
import Data.Map as Map

{-# FOREIGN AGDA2HS
{-# LANGUAGE StrictData #-}
#-}

{-----------------------------------------------------------------------------
    Customer
------------------------------------------------------------------------------}
-- | A 'Customer' is represented as a numerical ID.
--
-- The numerical ID ranges in 'Word31' because that is the range
-- for a step in address derivation, see 'BIP32Path'.
Customer = Word31

{-# COMPILE AGDA2HS Customer #-}

{-----------------------------------------------------------------------------
    Address derivation
------------------------------------------------------------------------------}
-- | Description of the derivation path used for the Deposit Wallet:
-- Either a 'Customer' or a change address.
data DerivationPath : Set where
  DerivationCustomer : Customer → DerivationPath
  DerivationChange   : DerivationPath

{-# COMPILE AGDA2HS DerivationPath #-}

-- | Full 'BIP32Path' corresponding to a 'DerivationPath'.
toBIP32Path : DerivationPath → BIP32Path
toBIP32Path = addSuffix prefix
  where
    prefix =
      (BIP32Path.Segment
      (BIP32Path.Segment
      (BIP32Path.Segment
        BIP32Path.Root
        Hardened 1857) -- Address derivation standard
        Hardened 1815) -- ADA
        Hardened 0)    -- account

    addSuffix : BIP32Path → DerivationPath → BIP32Path
    addSuffix path DerivationChange =
        (BIP32Path.Segment
        (BIP32Path.Segment
          path
          Soft 1)
          Soft 0)
    addSuffix path (DerivationCustomer c) =
        (BIP32Path.Segment
        (BIP32Path.Segment
          path
          Soft 0)
          Soft c)

{-# COMPILE AGDA2HS toBIP32Path #-}

-- | Perform two soft derivation steps.
deriveXPubSoft2 : XPub → Word31 → Word31 → XPub
deriveXPubSoft2 xpub ix iy =
  (deriveXPubSoft
  (deriveXPubSoft xpub
    ix)
    iy)

{-# COMPILE AGDA2HS deriveXPubSoft2 #-}

-- | Perform soft derivation from a 'DerivationPath'. 
xpubFromDerivationPath : XPub → DerivationPath → XPub
xpubFromDerivationPath xpub DerivationChange =
  deriveXPubSoft2 xpub 1 0
xpubFromDerivationPath xpub (DerivationCustomer c) =
  deriveXPubSoft2 xpub 0 c

{-# COMPILE AGDA2HS xpubFromDerivationPath #-}

-- | Derive an address from the wallet public key.
--
-- (Internal, exported for technical reasons.)
deriveAddress : NetworkTag → XPub → DerivationPath → Address
deriveAddress net xpub =
  compactAddrFromEnterpriseAddr
  ∘ EnterpriseAddrC net
  ∘ credentialFromXPub
  ∘ xpubFromDerivationPath xpub

{-# COMPILE AGDA2HS deriveAddress #-}

-- | Derive an address for a customer from the wallet public key.
deriveCustomerAddress : NetworkTag → XPub → Customer → Address
deriveCustomerAddress net xpub c =
  deriveAddress net xpub (DerivationCustomer c)

{-# COMPILE AGDA2HS deriveCustomerAddress #-}

--
prop-deriveXPubSoft2-injective
  : ∀ {xpub : XPub} {ix1 ix2 iy1 iy2 : Word31}
  → deriveXPubSoft2 xpub ix1 iy1 ≡ deriveXPubSoft2 xpub ix2 iy2
  → ix1 ≡ ix2 ⋀ iy1 ≡ iy2
--
prop-deriveXPubSoft2-injective eq =
  let (eqxpub `and` eqy) = prop-deriveXPubSoft-injective _ _ _ _ eq
  in  (projr (prop-deriveXPubSoft-injective _ _ _ _ eqxpub)) `and` eqy

--
prop-xpubFromDerivationPath-injective
  : ∀ {xpub : XPub} {x y : DerivationPath}
  → xpubFromDerivationPath xpub x ≡ xpubFromDerivationPath xpub y
  → x ≡ y
--
prop-xpubFromDerivationPath-injective {_} {DerivationCustomer x} {DerivationCustomer y} eq =
  cong DerivationCustomer (projr (prop-deriveXPubSoft-injective _ _ _ _ eq))
prop-xpubFromDerivationPath-injective {_} {DerivationCustomer x} {DerivationChange} eq =
  case projr (prop-deriveXPubSoft-injective _ _ _ _ (projl (prop-deriveXPubSoft-injective _ _ _ _ eq))) of λ ()
prop-xpubFromDerivationPath-injective {_} {DerivationChange} {DerivationCustomer y} eq =
  case projr (prop-deriveXPubSoft-injective _ _ _ _ (projl (prop-deriveXPubSoft-injective _ _ _ _ eq))) of λ ()
prop-xpubFromDerivationPath-injective {_} {DerivationChange} {DerivationChange} eq =
  refl

--
lemma-EnterpriseAddrC-injective
  : ∀ {net : NetworkTag} (x1 y1 : Credential)
  → EnterpriseAddrC net x1 ≡ EnterpriseAddrC net y1
  → x1 ≡ y1
--
lemma-EnterpriseAddrC-injective _ _ refl = refl

--
@0 prop-deriveAddress-injective
  : ∀ {net : NetworkTag} {xpub : XPub} {x y : DerivationPath}
  → deriveAddress net xpub x ≡ deriveAddress net xpub y
  → x ≡ y
--
prop-deriveAddress-injective {net} =
  prop-xpubFromDerivationPath-injective
  ∘ prop-credentialFromXPub-injective _ _
  ∘ lemma-EnterpriseAddrC-injective _ _
  ∘ prop-compactAddrFromEnterpriseAddr-injective _ _

--
@0 lemma-derive-notCustomer
  : ∀ {net : NetworkTag} (xpub : XPub) (c : Customer)
  → ¬(deriveAddress net xpub DerivationChange
      ≡ deriveCustomerAddress net xpub c)
--
lemma-derive-notCustomer {net} xpub c eq =
    bang (prop-deriveAddress-injective {net} {xpub} eq)
  where
    bang : DerivationChange ≡ DerivationCustomer c → ⊥
    bang ()

{-----------------------------------------------------------------------------
    Type definition
------------------------------------------------------------------------------}
-- | Data type that keeps track of addresses
-- that belong to the Deposit Wallet.
--
-- NOTE: The fields are mean to be read-only,
-- they are exported for technical reasons.
record AddressState : Set where
  constructor AddressStateC
  field
    networkId : NetworkId
    stateXPub : XPub
    addresses : Map.Map Address Customer
--    customers : Map.Map Customer Address
    customerCount : Word31

    change    : Address

  @0 networkTag : NetworkTag
  networkTag = fromNetworkId networkId

  field
    @0 invariant-change
      : change ≡ deriveAddress networkTag stateXPub DerivationChange

    @0 invariant-customer
      : ∀ (addr : Address) (c : Customer)
      → Map.lookup addr addresses ≡ Just c
      → addr ≡ deriveCustomerAddress networkTag stateXPub c

open AddressState public

postulate instance
  iShowAddressState : Show AddressState

-- | Network for which this 'AddressState' tracks addresses.
getNetworkTag : AddressState → NetworkTag
getNetworkTag s = fromNetworkId (networkId s)

-- | Public key of the wallet.
getXPub : AddressState → XPub
getXPub = stateXPub

-- | Efficient test whether an 'Address' belongs to a known 'Customer'.
isCustomerAddress : AddressState → Address → Bool
isCustomerAddress s = λ addr → isJust $ Map.lookup addr (addresses s)

-- | Efficient test whether an 'Address' is an internal change address.
isChangeAddress : AddressState → Address → Bool
isChangeAddress = λ s addr → change s == addr

-- | Test whether an 'Address' belongs to the wallet.
-- This can be an address of a 'Customer', or an internal change address.
isOurs : AddressState → Address → Bool
isOurs = λ s addr → isChangeAddress s addr || isCustomerAddress s addr

{-# COMPILE AGDA2HS AddressState #-}
{-# COMPILE AGDA2HS iShowAddressState derive #-}
{-# COMPILE AGDA2HS getNetworkTag #-}
{-# COMPILE AGDA2HS getXPub #-}
{-# COMPILE AGDA2HS isCustomerAddress #-}
{-# COMPILE AGDA2HS isChangeAddress #-}
{-# COMPILE AGDA2HS isOurs #-}

{-----------------------------------------------------------------------------
    Invariants
------------------------------------------------------------------------------}
-- | Lookup a derivation path from a change address and a map of addresses.
lookupDerivationPathFun
  : Address
  → Map.Map Address Customer
  → Address
  → Maybe DerivationPath
lookupDerivationPathFun change' addresses' addr =
  if change' == addr
  then Just DerivationChange
  else DerivationCustomer <$> Map.lookup addr addresses'

-- | Test whether an 'Address' is known and look up its 'DerivationPath'.
lookupDerivationPath : AddressState → Address → Maybe DerivationPath
lookupDerivationPath s addr =
    lookupDerivationPathFun (change s) (addresses s) addr

{-# COMPILE AGDA2HS lookupDerivationPathFun #-}
{-# COMPILE AGDA2HS lookupDerivationPath #-}

--
@0 prop-lookup-DerivationPath-Just
  : ∀ (s : AddressState)
      (addr : Address)
      (path : DerivationPath)
  → lookupDerivationPath s addr ≡ Just path
  → addr ≡ deriveAddress (networkTag s) (stateXPub s) path
--
prop-lookup-DerivationPath-Just s addr path
  with (change s == addr) in eqChange
  with Map.lookup addr (addresses s) in eqMap
... | False | Just c =
    λ { refl → invariant-customer s addr c eqMap }
... | True  | r =
    λ { refl → trans (sym (equality _ _ eqChange)) (invariant-change s) }

--
@0 prop-lookupDerivationPath-isOurs
  : ∀ (s : AddressState)
      (addr : Address)
  → isJust (lookupDerivationPath s addr) ≡ isOurs s addr
--
prop-lookupDerivationPath-isOurs s addr
  with (change s == addr)
  with Map.lookup addr (addresses s)
... | True | r = refl
... | False | Nothing = refl
... | False | Just c = refl

-- | If an address is a known customer address,
-- then it was derived from a 'Customer' ID.
--
@0 prop-isCustomerAddress-deriveCustomerAddress
  : ∀ (s : AddressState)
      (addr : Address)
  → isCustomerAddress s addr ≡ True
  → ∃ (λ c → addr ≡ deriveCustomerAddress (getNetworkTag s) (getXPub s) c)
--
prop-isCustomerAddress-deriveCustomerAddress s addr
  with Map.lookup addr (addresses s) in eq
... | Just c = λ refl → c `witness` invariant-customer s addr c eq

-- | If known customer address belongs to the wallet.
--
@0 prop-isOurs-from-isCustomerAddress
  : ∀ (s : AddressState)
      (addr : Address)
  → isCustomerAddress s addr ≡ True
  → isOurs s addr ≡ True
--
prop-isOurs-from-isCustomerAddress s addr eq
  rewrite eq = prop-x-||-True _

-- | It's ours if it's an internal change address or a known
-- customer address.
--
@0 prop-isOurs
  : ∀ (s : AddressState)
      (addr : Address)
  → isOurs s addr
    ≡ (isChangeAddress s addr || isCustomerAddress s addr)
--
prop-isOurs s addr = refl

{-----------------------------------------------------------------------------
    Observations, basic
------------------------------------------------------------------------------}
--
@0 lemma-change-not-known
  : ∀ (s : AddressState)
  → Map.lookup (change s) (addresses s) ≡ Nothing
--
lemma-change-not-known s
  with Map.lookup (change s) (addresses s) in eq
... | Just c =
      case lemma-derive-notCustomer xpub c lem1 of λ ()
    where
      net = getNetworkTag s
      xpub = stateXPub s

      lem1 =
        begin
          deriveAddress net xpub DerivationChange
        ≡⟨ sym (invariant-change s) ⟩
          change s
        ≡⟨ invariant-customer s (change s) c eq ⟩
          deriveCustomerAddress net xpub c
        ∎
... | Nothing = refl

--
@0 lemma-isChange-not-isCustomer
  : ∀ (s : AddressState)
      (addr : Address)
  → isChangeAddress s addr ≡ True
  → isCustomerAddress s addr ≡ False
--
lemma-isChange-not-isCustomer s a eq =
  begin
    isCustomerAddress s a
  ≡⟨ cong (isCustomerAddress s) (sym (equality _ _ eq)) ⟩
    isCustomerAddress s (change s)
  ≡⟨ cong isJust (lemma-change-not-known s) ⟩
    False
  ∎

--
lemma-contra-Bool
  : ∀ (x y : Bool)
  → (x ≡ True → y ≡ False)
  → (y ≡ True → x ≡ False)
--
lemma-contra-Bool False False impl1 = λ _ → refl
lemma-contra-Bool False True impl1 = λ _ → refl
lemma-contra-Bool True False impl1 = λ ()
lemma-contra-Bool True True impl1 = λ _ → impl1 refl

--
@0 lemma-isCustomer-not-isChange
  : ∀ (s : AddressState)
      (addr : Address)
  → isCustomerAddress s addr ≡ True
  → isChangeAddress s addr ≡ False
--
lemma-isCustomer-not-isChange s addr =
    lemma-contra-Bool _ _ (lemma-isChange-not-isCustomer s addr)

{-----------------------------------------------------------------------------
    Observations, BIP32
------------------------------------------------------------------------------}
-- | Retrieve the full 'BIP32Path' of a known 'Address'.
--
-- Returns 'Nothing' if the address is not from a known 'Customer'
-- or not equal to an internal change address.
getBIP32Path : AddressState → Address → Maybe BIP32Path
getBIP32Path s = fmap toBIP32Path ∘ lookupDerivationPath s

{-# COMPILE AGDA2HS getBIP32Path #-}

-- TODO: Property that relates BIP32Path to address.

{-----------------------------------------------------------------------------
    Observations, specification
------------------------------------------------------------------------------}

-- | Helper function
--
-- (Internal, exported for technical reasons.)
swap : ∀ {a b : Set} → a × b → b × a
swap (x , y) = (y , x)

-- Specification
-- | List all known associations between 'Customer's and their 'Address'es.
listCustomers : AddressState → List (Customer × Address)
listCustomers =
    map swap ∘ Map.toAscList ∘ addresses

-- | Test whether an 'Address' is a customer address.
knownCustomerAddress : Address → AddressState → Bool
knownCustomerAddress address =
    elem address ∘ map snd ∘ listCustomers

-- alternate definition
knownCustomerAddress' : Address → AddressState → Bool
knownCustomerAddress' address =
    elem address ∘ map fst ∘ Map.toAscList ∘ addresses

{-# COMPILE AGDA2HS swap #-}
{-# COMPILE AGDA2HS listCustomers #-}
{-# COMPILE AGDA2HS knownCustomerAddress #-}

--
-- alternate definition and original definition coincide
lemma-known-known'
  : ∀ (s : AddressState)
      (addr : Address)
  → knownCustomerAddress addr s
    ≡ knownCustomerAddress' addr s
--
lemma-known-known' s a =
  begin
    (elem a ∘ map snd ∘ listCustomers) s
  ≡⟨⟩
    (elem a ∘ map snd ∘ map swap ∘ Map.toAscList ∘ addresses) s
  ≡⟨ cong (elem a) (sym (map-∘ snd swap (Map.toAscList (addresses s)))) ⟩
    (elem a ∘ map (snd ∘ swap) ∘ Map.toAscList ∘ addresses) s
  ≡⟨⟩
    (elem a ∘ map fst ∘ Map.toAscList ∘ addresses) s
  ∎

--
lemma-isCustomerAddress-knownCustomerAddress'
  : ∀ (s : AddressState)
      (addr : Address)
  → isCustomerAddress s addr
    ≡ knownCustomerAddress' addr s
--
lemma-isCustomerAddress-knownCustomerAddress' s addr
  = sym (Map.prop-elem-keys addr (addresses s))

--
@0 lemma-isCustomerAddress-knownCustomerAddress
  : ∀ (s : AddressState)
      (addr : Address)
  → isCustomerAddress s addr
    ≡ knownCustomerAddress addr s
--
lemma-isCustomerAddress-knownCustomerAddress s addr =
  begin
    isCustomerAddress s addr
  ≡⟨ lemma-isCustomerAddress-knownCustomerAddress' s addr ⟩
    knownCustomerAddress' addr s
  ≡⟨ sym (lemma-known-known' s addr ) ⟩
    knownCustomerAddress addr s
  ∎

{-----------------------------------------------------------------------------
    Observations
------------------------------------------------------------------------------}
-- | Total number of known 'Customer's.
getKnownCustomerCount : AddressState → Word31
getKnownCustomerCount = customerCount

{-# COMPILE AGDA2HS getKnownCustomerCount #-}

{-----------------------------------------------------------------------------
    Operations
    Create address
------------------------------------------------------------------------------}

-- | Looking up a key that was just inserted will return that key/element.
--
lemma-lookup-insert-same
  : ∀ (k : Address)
      (x : Customer)
      (m : Map.Map Address Customer)
  → Map.lookup k (Map.insert k x m) ≡ Just x
--
lemma-lookup-insert-same a c m =
  begin
    Map.lookup a (Map.insert a c m)
  ≡⟨ Map.prop-lookup-insert a a c m ⟩
    (if (a == a) then Just c else Map.lookup a m)
  ≡⟨ cong (λ b → if b then Just c else Map.lookup a m) (equality' a a refl) ⟩
    (if True then Just c else Map.lookup a m)
  ≡⟨⟩
    Just c
  ∎

-- Specification
-- | Create a new associated between 'Customer' and known 'Address'.
createAddress : Customer → AddressState → (Address × AddressState)
createAddress c s0 = ( addr , s1 )
  where
    xpub = stateXPub s0
    net = getNetworkTag s0
    addr = deriveCustomerAddress net xpub c

    addresses1 : Map.Map Address Customer
    addresses1 = Map.insert addr c (addresses s0)

    @0 lem
      : ∀ (addr2 : Address) (c2 : Customer)
      → Map.lookup addr2 addresses1 ≡ Just c2
      → addr2 ≡ deriveCustomerAddress net xpub c2
    lem addr2 c2 eq
      with addr2 == addr in eqAddr
    ... | True =
          begin
            addr2
          ≡⟨ equality _ _ eqAddr ⟩
            addr
          ≡⟨⟩
            deriveCustomerAddress net xpub c
          ≡⟨ cong (λ o → deriveCustomerAddress net xpub o) (prop-Just-injective _ _ (trans (sym lem31) eq)) ⟩
            deriveCustomerAddress net xpub c2
          ∎
        where
          lem31 =
            begin
              Map.lookup addr2 addresses1
            ≡⟨ cong (λ o → Map.lookup o addresses1) (equality _ _ eqAddr) ⟩
              Map.lookup addr addresses1
            ≡⟨ lemma-lookup-insert-same addr c (addresses s0) ⟩
              Just c
            ∎
    ... | False = invariant-customer s0 addr2 c2 (trans (sym lem32) eq)
        where
          lem32
            : Map.lookup addr2 addresses1
              ≡ Map.lookup addr2 (addresses s0)
          lem32 =
            begin
              Map.lookup addr2 addresses1
            ≡⟨ Map.prop-lookup-insert _ _ c (addresses s0) ⟩
              (if (addr2 == addr) then Just c else Map.lookup addr2 (addresses s0))
            ≡⟨ cong (λ b → if b then Just c else Map.lookup addr2 (addresses s0)) eqAddr ⟩
              (if False then Just c else Map.lookup addr2 (addresses s0))
            ≡⟨⟩
              Map.lookup addr2 (addresses s0)
            ∎

    s1 : AddressState
    s1 = record
      { networkId = networkId s0
      ; stateXPub = stateXPub s0
      ; addresses = addresses1
      ; customerCount = 0 -- FIXME: Remove `createAddress`
      ; change = change s0
      ; invariant-change = invariant-change s0
      ; invariant-customer = lem
      }

{-# COMPILE AGDA2HS createAddress #-}

{-----------------------------------------------------------------------------
    Operations
    Construction
------------------------------------------------------------------------------}

-- | Create an empty 'AddressState' for a given 'NetworkId' from a public key.
emptyFromXPub : NetworkId → XPub → AddressState
emptyFromXPub net xpub =
  record
    { networkId = net
    ; stateXPub = xpub
    ; addresses = Map.empty
    ; customerCount = 0
    ; change = deriveAddress (fromNetworkId net) xpub DerivationChange
    ; invariant-change = refl
    ; invariant-customer = λ addr c eq →
      case trans (sym eq) (Map.prop-lookup-empty addr) of λ ()
    }

{-# COMPILE AGDA2HS emptyFromXPub #-}

-- | Create an 'AddressState' for a given 'NetworkId' from a public key and
-- a customer count.
fromXPubAndCount : NetworkId → XPub → Word31 → AddressState
fromXPubAndCount net xpub count =
    record s1' { customerCount = count}
  where
    s0 = emptyFromXPub net xpub

    customers : List Customer
    customers =
      if fromEnum count == 0
      then []
      else λ {{neq}} →
        let @0 notMin : _
            notMin = subst IsFalse (sym neq) IsFalse.itsFalse
        in  enumFromTo 0 (pred count {{notMin}})

    s1' = foldl (λ s c → snd (createAddress c s)) s0 customers

{-# COMPILE AGDA2HS fromXPubAndCount #-}

{-----------------------------------------------------------------------------
    Operations
    Change address generation
------------------------------------------------------------------------------}

-- | Change address generator employed by 'AddressState'.
newChangeAddress : AddressState → ChangeAddressGen ⊤
newChangeAddress s = λ _ → (change s , tt)

{-# COMPILE AGDA2HS newChangeAddress #-}

--
lemma-isChange-isChangeAddress
  : ∀ (s : AddressState)
      (addr : Address)
  → isChange (newChangeAddress s) addr
  → isChangeAddress s addr ≡ True
--
lemma-isChange-isChangeAddress s addr (_c0 `witness` eq) =
  equality' _ _ eq

-- | /Essential property./
--
-- Customer addresses are never change addresses.
@0 prop-changeAddress-not-Customer
  : ∀ (s : AddressState)
      (addr : Address)
  → knownCustomerAddress addr s ≡ True
  → ¬(isChange (newChangeAddress s) addr)
--
prop-changeAddress-not-Customer s addr eq-known eq-change =
    bang lem4
  where
    lem1 : isCustomerAddress s addr ≡ True
    lem1 = trans (lemma-isCustomerAddress-knownCustomerAddress s addr) eq-known

    lem2 : isChangeAddress s addr ≡ False
    lem2 = lemma-isCustomer-not-isChange s addr lem1

    lem3 : isChangeAddress s addr ≡ True
    lem3 = lemma-isChange-isChangeAddress s addr eq-change

    lem4 : False ≡ True
    lem4 = trans (sym lem2) lem3

    bang : False ≡ True → ⊥
    bang ()

{-----------------------------------------------------------------------------
    Operations
    Mock change address
------------------------------------------------------------------------------}
-- | Mock address of maximum length
--
-- This address is used by the coin selection algorithm
-- to get the transaction fees right.
-- Addresses created by 'newChangeAddress' are required to be no longer
-- than this address.
-- This address should not be used in a transaction.
mockMaxLengthChangeAddress : AddressState → Address
mockMaxLengthChangeAddress s =
  compactAddrFromEnterpriseAddr
  ∘ EnterpriseAddrC (getNetworkTag s)
  ∘ credentialFromXPub
  $ deriveXPubSoft2 (stateXPub s) 17 0

{-# COMPILE AGDA2HS mockMaxLengthChangeAddress #-}

-- | 'mockMaxLengthChangeAddress' never belongs to the 'AddressState'.
--
@0 prop-isOurs-mockMaxLengthChangeAddress-False
  : ∀ (s : AddressState)
  → isOurs s (mockMaxLengthChangeAddress s) ≡ False
--
prop-isOurs-mockMaxLengthChangeAddress-False s
  with lookupDerivationPath s (mockMaxLengthChangeAddress s) in eq
... | Nothing =
    trans (sym (prop-lookupDerivationPath-isOurs s _)) (cong isJust eq)
... | Just path =
    case lem3 path (prop-lookup-DerivationPath-Just s _ path eq) of λ ()
  where
    addr = mockMaxLengthChangeAddress s

    lem1
      : addr ≡ deriveAddress (networkTag s) (stateXPub s) DerivationChange
      → 17 ≡ 1
    lem1 =
      projl
      ∘ prop-deriveXPubSoft2-injective
      ∘ prop-credentialFromXPub-injective _ _
      ∘ lemma-EnterpriseAddrC-injective _ _
      ∘ prop-compactAddrFromEnterpriseAddr-injective _ _
    
    lem2
      : (c : Customer)
      → addr ≡ deriveAddress (networkTag s) (stateXPub s) (DerivationCustomer c)
      → 17 ≡ 0
    lem2 c =
      projl
      ∘ prop-deriveXPubSoft2-injective
      ∘ prop-credentialFromXPub-injective _ _
      ∘ lemma-EnterpriseAddrC-injective _ _
      ∘ prop-compactAddrFromEnterpriseAddr-injective _ _

    lem3
      : (path : DerivationPath)
      → addr ≡ deriveAddress (networkTag s) (stateXPub s) path
      → ⊥
    lem3 (DerivationCustomer c) eq = case lem2 c eq of λ ()
    lem3 DerivationChange eq = case lem1 eq of λ ()
