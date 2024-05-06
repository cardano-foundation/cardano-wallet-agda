{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.Encoding
    {-
    ; mkEnterpriseAddress
    ; prop-mkEnterpriseAddress-injective
    -}
    where

open import Haskell.Prelude

open import Cardano.Wallet.Address.BIP32_Ed25519 using
  ( XPub
  ; rawSerialiseXPub
  ; prop-rawSerialiseXPub-injective
  )
open import Cardano.Wallet.Address.Hash using
  ( blake2b'224
  ; prop-blake2b'224-injective
  )
open import Cardano.Wallet.Deposit.Read using
  ( Addr
  )
open import Haskell.Data.ByteString using
  ( ByteString
  ; singleton
  ; prop-<>-cancel-left
  )
open import Haskell.Data.Word using
  ( Word8
  )

{-----------------------------------------------------------------------------
    Create addresses from public keys

    For magic numbers, see
    https://github.com/cardano-foundation/CIPs/tree/master/CIP-0019
------------------------------------------------------------------------------}

tagEnterprise : Word8 
tagEnterprise = 0b01100001

{-# COMPILE AGDA2HS tagEnterprise #-}

mkEnterpriseAddress : XPub → Addr
mkEnterpriseAddress xpub =
    singleton tagEnterprise <> blake2b'224 (rawSerialiseXPub xpub)

{-# COMPILE AGDA2HS mkEnterpriseAddress #-}

{-----------------------------------------------------------------------------
    Properties
------------------------------------------------------------------------------}

prop-mkEnterpriseAddress-injective
  : ∀ (x y : XPub)
  → mkEnterpriseAddress x ≡ mkEnterpriseAddress y
  → x ≡ y
prop-mkEnterpriseAddress-injective x y =
  prop-rawSerialiseXPub-injective _ _
    ∘ prop-blake2b'224-injective _ _
    ∘ prop-<>-cancel-left (singleton tagEnterprise) _ _
