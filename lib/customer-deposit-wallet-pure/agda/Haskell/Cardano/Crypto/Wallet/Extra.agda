{-# OPTIONS --erasure #-}

module Haskell.Cardano.Crypto.Wallet.Extra where

open import Haskell.Prelude hiding (fromJust)

open import Haskell.Data.Word using
  ( Word32
  )
open import Haskell.Data.Word.Odd using
  ( Word31
  )
open import Haskell.Data.ByteString using
  ( ByteString
  ; empty
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

  xpub : ByteString → Either String XPub
  xprv : ByteString → Either String XPrv
  xsignature : ByteString → Either String XSignature

  xpubPublicKey : XPub → ByteString
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

{-----------------------------------------------------------------------------
    Properties
    xPrvChangePass
------------------------------------------------------------------------------}
-- | Password changes with 'xPrvChangePass' are reflexive.
postulate
 prop-xPrvChangePass-refl
  : ∀ (pa : ByteString) (xprv : XPrv)
  → xPrvChangePass pa pa xprv
    ≡ xprv

-- | Password changes with 'xPrvChangePass' are transitive.
postulate
 prop-xPrvChangePass-trans
  : ∀ (pa pb pc : ByteString) (xprv : XPrv)
  → xPrvChangePass pa pb (xPrvChangePass pb pc xprv)
    ≡ xPrvChangePass pa pc xprv

-- | Password changes with 'xPrvChangePass'
-- commute with 'sign'.
postulate
 prop-sign-xPrvChangePass
  : ∀ (pa pb : ByteString) (xprv : XPrv) (msg : ByteString)
  → sign pb (xPrvChangePass pa pb xprv) msg
    ≡ sign pa xprv msg

-- | Password needs to be changed to the empty 'ByteString'
-- to get the correct 'XPub'.
postulate
 prop-verify-xPrvChangePass
  : ∀ (xprv : XPrv) (pass : ByteString) (msg : ByteString)
  → let xpub = toXPub (xPrvChangePass pass empty xprv)
    in  verify xpub msg (sign pass xprv msg)
          ≡ True

-- | Password changes with 'xPrvChangePass'
-- commute with 'deriveXPrv'.
postulate
  prop-deriveXPrv-xPrvChangePass
   : ∀ (pa pb : ByteString) (xprv : XPrv) (ix : Word32)
   → deriveXPrv DerivationScheme2 pb (xPrvChangePass pa pb xprv) ix
     ≡ xPrvChangePass pa pb (deriveXPrv DerivationScheme2 pa xprv ix)

{-----------------------------------------------------------------------------
    Properties
    Serialization
------------------------------------------------------------------------------}
-- | 'xpub' always deserializes 'unXPub'.
postulate
  prop-xpub-unXPub
    : ∀ (x : XPub)
    → xpub (unXPub x) ≡ Right x

-- | 'xprv' always deserializes 'unXPrv'.
postulate
  prop-xprv-unXPrv
    : ∀ (x : XPrv)
    → xprv (unXPrv x) ≡ Right x

-- | 'xsignature' always deserializes 'unXSignature'.
postulate
  prop-xsignature-unXSignature
    : ∀ (x : XSignature)
    → xsignature (unXSignature x) ≡ Right x
