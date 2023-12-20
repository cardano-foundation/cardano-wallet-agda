{-# OPTIONS --erasure #-}

-- Address management for the Customer Deposit Wallet
module Cardano.Wallet.Deposit.Pure.Address
    {-
    ; deriveAddress
    ; Customer
      ; deriveCustomerAddress
    ; AddressState
      ; listCustomers
      ; knownCustomerAddress

      ; createAddress

      ; newChangeAddress
      ; prop-changeAddress-not-Customer
    -}
    where

open import Haskell.Prelude
open import Haskell.Reasoning

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

import Haskell.Data.Map as Map

{-----------------------------------------------------------------------------
    Assumptions
------------------------------------------------------------------------------}

Customer = Nat

deriveAddress : Nat → Address
deriveAddress ix = suc ix

deriveCustomerAddress : Customer → Address
deriveCustomerAddress c = deriveAddress (suc c)

--
@0 lemma-derive-injective
  : ∀ {x y : Nat}
  → deriveAddress x ≡ deriveAddress y
  → x ≡ y
--
lemma-derive-injective refl = refl

--
@0 lemma-derive-notCustomer
  : ∀ (c : Customer)
  → ¬(deriveAddress 0 ≡ deriveCustomerAddress c)
--
lemma-derive-notCustomer c eq = bang (lemma-derive-injective eq)
  where
    bang : 0 ≡ suc c → ⊥
    bang ()

{-----------------------------------------------------------------------------
    Type definition
------------------------------------------------------------------------------}

record AddressState : Set where
  field
    addresses : Map.Map Address Customer
--    customers : Map.Map Customer Address

    change    : Address

  isCustomerAddress : Address → Bool
  isCustomerAddress = λ addr → isJust $ Map.lookup addr addresses

  field
    @0 invariant-change
      : change ≡ deriveAddress 0

    @0 invariant-customer
      : ∀ (addr : Address)
      → isCustomerAddress addr ≡ True
      → ∃ (λ ix → addr ≡ deriveCustomerAddress ix)

open AddressState

{-----------------------------------------------------------------------------
    Observations, basic
------------------------------------------------------------------------------}

-- isCustomerAddress : AddressState → Address → Bool

isChangeAddress : AddressState → Address → Bool
isChangeAddress = λ s addr → change s == addr

isOurs : AddressState → Address → Bool
isOurs = λ s addr → isChangeAddress s addr || isCustomerAddress s addr

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

            lem1 : deriveAddress 0 ≡ deriveCustomerAddress ix
            lem1 = trans (sym (invariant-change s)) eq
        in  magic (lemma-derive-notCustomer ix lem1)
    ; Nothing {{eq}} → eq
    }

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
    addr = deriveCustomerAddress c

    addresses1 = Map.insert addr c (addresses s0)

    @0 lem2
      : ∀ (addr2 : Address)
      → isJust (Map.lookup addr2 addresses1) ≡ True
      → ∃ (λ ix → addr2 ≡ deriveCustomerAddress ix)
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
      { addresses = addresses1
      ; change = change s0
      ; invariant-change = invariant-change s0
      ; invariant-customer = lem2
      }

{-----------------------------------------------------------------------------
    Operations
    Change address generation
------------------------------------------------------------------------------}

newChangeAddress : AddressState → ChangeAddressGen ⊤
newChangeAddress s = λ _ → (change s , tt)

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
 