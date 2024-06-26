{-# OPTIONS --erasure #-}

-- Address management for the Customer Deposit Wallet
module Cardano.Wallet.Deposit.Pure.Address
    {-
    ; deriveAddress
    ; Customer
      ; deriveCustomerAddress
    ; AddressState
      ; isOurs
      ; listCustomers
      ; knownCustomerAddress

      ; createAddress
      ; prop-create-derive
      ; prop-create-known

      ; fromXPubAndCount
      ; getXPub

      ; newChangeAddress
      ; prop-changeAddress-not-Customer
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
    ( mkEnterpriseAddress
    ; prop-mkEnterpriseAddress-injective
    )
open import Cardano.Wallet.Deposit.Read using
    ( Address
    )
open import Cardano.Write.Tx.Balance using
    ( ChangeAddressGen
    ; isChange
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
import Haskell.Data.Map as Map

{-----------------------------------------------------------------------------
    Assumptions
------------------------------------------------------------------------------}

Customer = Word31

{-# COMPILE AGDA2HS Customer #-}

data DerivationPath : Set where
  DerivationCustomer : Customer → DerivationPath
  DerivationChange   : DerivationPath

{-# COMPILE AGDA2HS DerivationPath #-}

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
          path
          Soft 1)
    addSuffix path (DerivationCustomer c) =
        (BIP32Path.Segment
        (BIP32Path.Segment
          path
          Soft 0)
          Soft c)

{-# COMPILE AGDA2HS toBIP32Path #-}

xpubFromDerivationPath : XPub → DerivationPath → XPub
xpubFromDerivationPath xpub DerivationChange =
  (deriveXPubSoft xpub
    1)
xpubFromDerivationPath xpub (DerivationCustomer c) =
  (deriveXPubSoft
  (deriveXPubSoft xpub
    0)
    c)

{-# COMPILE AGDA2HS xpubFromDerivationPath #-}

deriveAddress : XPub → DerivationPath → Address
deriveAddress xpub = mkEnterpriseAddress ∘ xpubFromDerivationPath xpub

{-# COMPILE AGDA2HS deriveAddress #-}

deriveCustomerAddress : XPub → Customer → Address
deriveCustomerAddress xpub c = deriveAddress xpub (DerivationCustomer c)

{-# COMPILE AGDA2HS deriveCustomerAddress #-}

--
@0 lemma-xpubFromDerivationPath-injective
  : ∀ {xpub : XPub} {x y : DerivationPath}
  → xpubFromDerivationPath xpub x ≡ xpubFromDerivationPath xpub y
  → x ≡ y
--
lemma-xpubFromDerivationPath-injective {_} {DerivationCustomer x} {DerivationCustomer y} eq =
  cong DerivationCustomer (projr (prop-deriveXPubSoft-injective _ _ _ _ eq))
lemma-xpubFromDerivationPath-injective {_} {DerivationCustomer x} {DerivationChange} eq =
  case (prop-deriveXPubSoft-not-identity _ _ (projl (prop-deriveXPubSoft-injective _ _ _ _ eq))) of λ ()
lemma-xpubFromDerivationPath-injective {_} {DerivationChange} {DerivationCustomer y} eq =
  case (prop-deriveXPubSoft-not-identity _ _ (sym (projl (prop-deriveXPubSoft-injective _ _ _ _ eq)))) of λ ()
lemma-xpubFromDerivationPath-injective {_} {DerivationChange} {DerivationChange} eq =
  case (prop-deriveXPubSoft-injective _ _ _ _ eq) of λ { (refl `and` refl) → refl }

--
@0 lemma-derive-injective
  : ∀ {xpub : XPub} {x y : DerivationPath}
  → deriveAddress xpub x ≡ deriveAddress xpub y
  → x ≡ y
--
lemma-derive-injective =
  lemma-xpubFromDerivationPath-injective
  ∘ prop-mkEnterpriseAddress-injective _ _

--
@0 lemma-derive-notCustomer
  : ∀ (xpub : XPub) (c : Customer)
  → ¬(deriveAddress xpub DerivationChange ≡ deriveCustomerAddress xpub c)
--
lemma-derive-notCustomer xpub c eq = bang (lemma-derive-injective {xpub} eq)
  where
    bang : DerivationChange ≡ DerivationCustomer c → ⊥
    bang ()

{-----------------------------------------------------------------------------
    Type definition
------------------------------------------------------------------------------}

record AddressState : Set where
  constructor AddressStateC
  field
    stateXPub : XPub
    addresses : Map.Map Address Customer
--    customers : Map.Map Customer Address

    change    : Address

  @0 isCustomerAddress₁ : Address → Bool
  isCustomerAddress₁ = λ addr → isJust $ Map.lookup addr addresses

  field
    @0 invariant-change
      : change ≡ deriveAddress stateXPub DerivationChange

    @0 invariant-customer
      : ∀ (addr : Address)
      → isCustomerAddress₁ addr ≡ True
      → ∃ (λ ix → addr ≡ deriveCustomerAddress stateXPub ix)

open AddressState public

isCustomerAddress : AddressState → Address → Bool
isCustomerAddress s = λ addr → isJust $ Map.lookup addr (addresses s)

{-# COMPILE AGDA2HS AddressState #-}
{-# COMPILE AGDA2HS isCustomerAddress #-}

{-----------------------------------------------------------------------------
    Observations, basic
------------------------------------------------------------------------------}

-- isCustomerAddress : AddressState → Address → Bool

isChangeAddress : AddressState → Address → Bool
isChangeAddress = λ s addr → change s == addr

isOurs : AddressState → Address → Bool
isOurs = λ s addr → isChangeAddress s addr || isCustomerAddress s addr

{-# COMPILE AGDA2HS isChangeAddress #-}
{-# COMPILE AGDA2HS isOurs #-}

suc-injective : ∀ {x y : Nat} → suc x ≡ suc y → x ≡ y
suc-injective refl = refl

--
@0 lemma-change-not-known
  : ∀ (s : AddressState)
  → Map.lookup (change s) (addresses s) ≡ Nothing
--
lemma-change-not-known s =
  case Map.lookup (change s) (addresses s) of λ
    { (Just _) {{eq}} →
        let (ix `witness` eq) =
              invariant-customer s (change s) (cong isJust eq)

            lem1 : deriveAddress xpub DerivationChange ≡ deriveCustomerAddress xpub ix
            lem1 = trans (sym (invariant-change s)) eq
        in  magic (lemma-derive-notCustomer xpub ix lem1)
    ; Nothing {{eq}} → eq
    }
  where
    xpub = stateXPub s

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

getDerivationPath'cases
  : AddressState → Address → Maybe Customer → Maybe DerivationPath
getDerivationPath'cases s addr (Just c) = Just (DerivationCustomer c)
getDerivationPath'cases s addr Nothing =
  if isChangeAddress s addr
  then Just DerivationChange
  else Nothing

getDerivationPath : AddressState → Address → Maybe DerivationPath
getDerivationPath s addr =
    getDerivationPath'cases s addr (Map.lookup addr (addresses s))

{-# COMPILE AGDA2HS getDerivationPath'cases #-}
{-# COMPILE AGDA2HS getDerivationPath #-}

getBIP32Path : AddressState → Address → Maybe BIP32Path
getBIP32Path s = fmap toBIP32Path ∘ getDerivationPath s

{-# COMPILE AGDA2HS getBIP32Path #-}

--
@0 lemma-getDerivationPath-Just
  : ∀ (s : AddressState)
      (addr : Address)
  → isOurs s addr ≡ True
  → ∃ (λ path → getDerivationPath s addr ≡ Just path)
--
lemma-getDerivationPath-Just s addr eq =
  case Map.lookup addr (addresses s) of λ
    { (Just c) {{eq1}} →
      DerivationCustomer c `witness`
        cong (getDerivationPath'cases s addr) eq1
    ; Nothing {{eq1}} →
      case isChangeAddress s addr of λ
        { True {{eq2}} → DerivationChange `witness`(
            begin
              getDerivationPath s addr
            ≡⟨ cong (getDerivationPath'cases s addr) eq1 ⟩
              (if (isChangeAddress s addr) then (Just DerivationChange) else Nothing)
            ≡⟨ cong (λ b → if b then _ else _) eq2 ⟩
              Just DerivationChange
            ∎
          )
        ; False {{eq2}} → case (prop-||-⋁ eq) of λ
          { (inl eqChange) →
            case trans (sym eqChange) eq2 of λ ()
          ; (inr eqCustomer) →
            case trans (sym eqCustomer) (cong isJust eq1) of λ () 
          }
        }
    }

{-----------------------------------------------------------------------------
    Observations, specification
------------------------------------------------------------------------------}

-- Helper function
swap : ∀ {a b : Set} → a × b → b × a
swap (x , y) = (y , x)

-- Specification
listCustomers : AddressState → List (Customer × Address)
listCustomers =
    map swap ∘ Map.toAscList ∘ addresses

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
@0 lemma-isCustomerAddress-knownCustomerAddress'
  : ∀ (s : AddressState)
      (addr : Address)
  → isCustomerAddress s addr
    ≡ knownCustomerAddress' addr s
--
lemma-isCustomerAddress-knownCustomerAddress' s addr
  = case Map.lookup addr (addresses s) of λ
    { (Just x) {{eq}} →
        begin
          isCustomerAddress s addr
        ≡⟨ cong isJust eq ⟩
          True
        ≡⟨ sym (Map.prop-lookup-toAscList-Just addr x (addresses s) eq) ⟩
          knownCustomerAddress' addr s
        ∎
    ; Nothing {{eq}} →
        begin
          isCustomerAddress s addr
        ≡⟨ cong isJust eq ⟩
          False
        ≡⟨ sym (Map.prop-lookup-toAscList-Nothing addr (addresses s) eq) ⟩
          knownCustomerAddress' addr s
        ∎
    }

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
    Operations
    Create address
------------------------------------------------------------------------------}

-- Specification
createAddress : Customer → AddressState → (Address × AddressState)
createAddress c s0 = ( addr , s1 )
  where
    xpub = stateXPub s0
    addr = deriveCustomerAddress xpub c

    addresses1 = Map.insert addr c (addresses s0)

    @0 lem2
      : ∀ (addr2 : Address)
      → isJust (Map.lookup addr2 addresses1) ≡ True
      → ∃ (λ ix → addr2 ≡ deriveCustomerAddress xpub ix)
    lem2 addr2 isMember = case addr2 == addr of λ
        { True {{eq}} → c `witness` equality addr2 addr eq
        ; False {{eq}} →
            let lem3
                  : Map.lookup addr2 addresses1
                  ≡ Map.lookup addr2 (addresses s0)
                lem3 =
                  begin
                    Map.lookup addr2 addresses1
                  ≡⟨ Map.prop-lookup-insert _ _ c (addresses s0) ⟩
                    (if (addr2 == addr) then Just c else Map.lookup addr2 (addresses s0))
                  ≡⟨ cong (λ b → if b then Just c else Map.lookup addr2 (addresses s0)) eq ⟩
                    (if False then Just c else Map.lookup addr2 (addresses s0))
                  ≡⟨⟩
                    Map.lookup addr2 (addresses s0)
                  ∎

                lem4 : isCustomerAddress s0 addr2 ≡ True
                lem4 = trans (cong (isJust) (sym lem3)) isMember
            in
                invariant-customer s0 addr2 lem4
        }

    s1 : AddressState
    s1 = record
      { stateXPub = stateXPub s0
      ; addresses = addresses1
      ; change = change s0
      ; invariant-change = invariant-change s0
      ; invariant-customer = lem2
      }

{-# COMPILE AGDA2HS createAddress #-}

--
prop-create-derive
  : ∀ (c : Customer)
      (s0 : AddressState)
  → let (address , _) = createAddress c s0
    in  deriveCustomerAddress (stateXPub s0) c ≡ address
--
prop-create-derive = λ c s0 → refl


-- lemma about converting == to ≡
--
lemma-lookup-insert-same
  : ∀ (a : Address)
      (c : Customer)
      (m : Map.Map Address Customer)
  → Map.lookup a (Map.insert a c m) ≡ Just c
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

--
@0 prop-create-known
  : ∀ (c  : Customer)
      (s0 : AddressState)
  → let (address , s1) = createAddress c s0
    in  knownCustomerAddress address s1 ≡ True
--
prop-create-known c s0 =
  let (a , s1) = createAddress c s0
  in
    begin
      knownCustomerAddress a s1
    ≡⟨ sym (lemma-isCustomerAddress-knownCustomerAddress s1 a) ⟩
      isCustomerAddress s1 a
    ≡⟨ cong isJust (lemma-lookup-insert-same a c (addresses s0)) ⟩
      True
    ∎

{-----------------------------------------------------------------------------
    Operations
    Construction
------------------------------------------------------------------------------}

getXPub : AddressState → XPub
getXPub = stateXPub

{-# COMPILE AGDA2HS getXPub #-}

-- | Create an empty 'AddressState' from a public key.
emptyFromXPub : XPub → AddressState
emptyFromXPub xpub =
  record
    { stateXPub = xpub
    ; addresses = Map.empty
    ; change = deriveAddress xpub DerivationChange
    ; invariant-change = refl
    ; invariant-customer = λ addr eq →
      case trans (sym eq) (cong isJust (Map.prop-lookup-empty addr)) of λ ()
    }

{-# COMPILE AGDA2HS emptyFromXPub #-}

-- | Create an 'AddressState' from a public key and
-- a number known customer addresses.
fromXPubAndCount : XPub → Word31 → AddressState
fromXPubAndCount xpub knownCustomerCount =
    foldl (λ s c → snd (createAddress c s)) s0 customers
  where
    s0 = emptyFromXPub xpub
    customers = enumFromTo 0 knownCustomerCount

{-# COMPILE AGDA2HS fromXPubAndCount #-}

{-----------------------------------------------------------------------------
    Operations
    Change address generation
------------------------------------------------------------------------------}

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

--
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
