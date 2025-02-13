{-# OPTIONS --erasure #-}

-- | Address derivation paths for
-- * Customer addresses
-- * Change addresses
-- * Mock addresses
-- and proofs.
module Cardano.Wallet.Deposit.Pure.Address.Customer where

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
open import Haskell.Data.Word.Odd using
    ( Word31
    ; word31FromNat
    )
open import Haskell.Data.Word.Odd public using
    ( iOrdWord31
    )

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
    for customer and change addresses
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
    Address derivation
    for mock addresses
------------------------------------------------------------------------------}
-- | Mock address of maximum length
--
-- This address is used by the coin selection algorithm
-- to get the transaction fees right.
-- Addresses created by 'newChangeAddress' are required to be no longer
-- than this address.
-- This address should not be used in a transaction.
deriveMockMaxLengthChangeAddress : NetworkTag → XPub → Address
deriveMockMaxLengthChangeAddress net xpub =
  compactAddrFromEnterpriseAddr
  ∘ EnterpriseAddrC net
  ∘ credentialFromXPub
  $ deriveXPubSoft2 xpub 17 0

{-# COMPILE AGDA2HS deriveMockMaxLengthChangeAddress #-}

--
@0 prop-mock-not-change
  : ∀ (net : NetworkTag) (xpub : XPub)
  → ¬(deriveAddress net xpub DerivationChange
      ≡ deriveMockMaxLengthChangeAddress net xpub)
--
prop-mock-not-change net xpub =
    nonsense
    ∘ projl
    ∘ prop-deriveXPubSoft2-injective
    ∘ prop-credentialFromXPub-injective _ _
    ∘ lemma-EnterpriseAddrC-injective _ _
    ∘ prop-compactAddrFromEnterpriseAddr-injective _ _
  where
    nonsense : 1 ≡ 17 → ⊥
    nonsense ()

--
@0 prop-mock-not-customer
  : ∀ (net : NetworkTag) (xpub : XPub) (c : Customer)
  → ¬(deriveAddress net xpub (DerivationCustomer c)
      ≡ deriveMockMaxLengthChangeAddress net xpub)
--
prop-mock-not-customer net xpub c =
    nonsense
    ∘ projl
    ∘ prop-deriveXPubSoft2-injective
    ∘ prop-credentialFromXPub-injective _ _
    ∘ lemma-EnterpriseAddrC-injective _ _
    ∘ prop-compactAddrFromEnterpriseAddr-injective _ _
  where
    nonsense : 0 ≡ 17 → ⊥
    nonsense ()

--
@0 prop-mock-not-deriveAddress
  : ∀ (net : NetworkTag) (xpub : XPub) (path : DerivationPath)
  → ¬(deriveAddress net xpub path
      ≡ deriveMockMaxLengthChangeAddress net xpub)
--
prop-mock-not-deriveAddress net xpub (DerivationCustomer c) =
    prop-mock-not-customer net xpub c
prop-mock-not-deriveAddress net xpub DerivationChange =
    prop-mock-not-change net xpub
