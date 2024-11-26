{-# OPTIONS --erasure #-}

-- Synchronized manually with the corresponding Haskell module.
module Haskell.Cardano.Crypto.Wallet where

open import Haskell.Prelude hiding (fromJust)

open import Haskell.Data.Word using
  ( Word32
  )
open import Haskell.Data.Word.Odd using
  ( Word31
  )
open import Haskell.Data.ByteString using
  ( ByteString
  )

postulate
  word32fromWord31Low : Word31 → Word32
  word32fromWord31High : Word31 → Word32

{-----------------------------------------------------------------------------
    Extended Private & Public keys
------------------------------------------------------------------------------}

data DerivationScheme : Set where
  DerivationScheme1 : DerivationScheme
  DerivationScheme2 : DerivationScheme

postulate
  XPub : Set
  XPrv : Set
  XSignature : Set

  unXPrv : XPrv → ByteString
  unXPub : XPub → ByteString
  unXSignature : XSignature → ByteString

  toXPub : XPrv → XPub
  xPrvChangePass : ByteString → ByteString → XPrv → XPrv

{-----------------------------------------------------------------------------
    Derivation Function
------------------------------------------------------------------------------}

postulate
  deriveXPrv : DerivationScheme → ByteString → XPrv → Word32 → XPrv
  deriveXPub : DerivationScheme → XPub → Word32 → Maybe XPub

{-----------------------------------------------------------------------------
    Signature & Verification from extended types
------------------------------------------------------------------------------}

postulate
  sign   : ByteString → XPrv → ByteString → XSignature
  verify : XPub → ByteString → XSignature → Bool
