{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.BIP32_Ed25519 where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.ByteString using
  ( ByteString
  )
open import Haskell.Data.Word.Odd using
  ( Word31
  )

{-# FOREIGN AGDA2HS
{-# LANGUAGE UnicodeSyntax #-}
import Data.ByteString
  ( ByteString
  )
import Data.Maybe
  ( fromJust
  )
import Data.Word
  ( Word32
  )
import Data.Word.Odd
  ( Word31
  )
import qualified Cardano.Crypto.Wallet as CC
import qualified Data.ByteString as BS
#-}

dummy : Int
dummy = 12 -- needed for Agda2hs to add sufficient imports

{-----------------------------------------------------------------------------
    Extended private and public keys
------------------------------------------------------------------------------}

-- TODO: Extend to encrypted keys
postulate
  XPub : Set  -- plaintext public key
  XPrv : Set  -- plaintext private key

  toXPub : XPrv → XPub

  XSignature : Set
  sign   : XPrv → ByteString → XSignature
  verify : XPub → ByteString → XSignature → Bool

  prop-verify-sign
    : ∀ (xprv : XPrv)
        (msg  : ByteString)
    → let xpub = toXPub xprv
      in  verify xpub msg (sign xprv msg) ≡ True

{-# FOREIGN AGDA2HS
-- FIXME: We define type synonyms here so that
-- they can be exported. Ideally, we would re-export from
-- the Cardano.Wallet.Crypto module.
type XPub = CC.XPub
type XPrv = CC.XPrv
type XSignature = CC.XSignature

toXPub :: XPrv → XPub
toXPub = CC.toXPub

sign :: XPrv → ByteString → XSignature
sign = CC.sign BS.empty

verify :: XPub → ByteString → XSignature → Bool
verify = CC.verify
#-}

postulate
  rawSerialiseXPub : XPub → ByteString
  rawSerialiseXPrv : XPrv → ByteString
  rawSerialiseXSignature : XSignature → ByteString

  prop-rawSerialiseXPub-injective
    : ∀ (x y : XPub)
    → rawSerialiseXPub x ≡ rawSerialiseXPub y
    → x ≡ y

{-# FOREIGN AGDA2HS
rawSerialiseXPub :: XPub → ByteString
rawSerialiseXPub = CC.unXPub

rawSerialiseXPrv :: XPrv → ByteString
rawSerialiseXPrv = CC.unXPrv

rawSerialiseXSignature :: XSignature → ByteString
rawSerialiseXSignature = CC.unXSignature
#-}

{-----------------------------------------------------------------------------
    Key derivation
------------------------------------------------------------------------------}

postulate
  deriveXPubSoft : XPub → Word31 → XPub
  deriveXPrvSoft : XPrv → Word31 → XPrv
  deriveXPrvHard : XPrv → Word31 → XPrv

postulate

  prop-derive-soft
    : ∀ (xprv : XPrv)
        (ix   : Word31)
    → deriveXPubSoft (toXPub xprv) ix
      ≡ toXPub (deriveXPrvSoft xprv ix)

  -- The following properties about injectivity
  -- are not true in the strict sense,
  -- only cryptographically hard.
  prop-deriveXPubSoft-injective
    : ∀ (xpub1 xpub2 : XPub)
        (ix1   ix2   : Word31)
    → deriveXPubSoft xpub1 ix1 ≡ deriveXPubSoft xpub2 ix2
    → (xpub1 ≡ xpub2 ⋀ ix1 ≡ ix2)

  prop-deriveXPubSoft-not-identity
    : ∀ (xpub : XPub) (ix : Word31)
    → ¬ (deriveXPubSoft xpub ix ≡ xpub)

  prop-deriveXPrvSoft-injective
    : ∀ (xprv    : XPrv)
        (ix1 ix2 : Word31)
    → deriveXPrvSoft xprv ix1 ≡ deriveXPrvSoft xprv ix2
    → ix1 ≡ ix2

  prop-deriveXPrvHard-injective
    : ∀ (xprv    : XPrv)
        (ix1 ix2 : Word31)
    → deriveXPrvHard xprv ix1 ≡ deriveXPrvHard xprv ix2
    → ix1 ≡ ix2

{-# FOREIGN AGDA2HS
word32fromWord31 :: Word31 → Word32
word32fromWord31 = fromInteger . toInteger

deriveXPubSoft :: XPub → Word31 → XPub
deriveXPubSoft xpub ix =
  fromJust 
    (CC.deriveXPub
      CC.DerivationScheme2
      xpub
      (word32fromWord31 ix)
    )
  -- deriveXPub always returns Just on Word31

deriveXPrvSoft :: XPrv → Word31 → XPrv
deriveXPrvSoft xprv ix = 
  CC.deriveXPrv
    CC.DerivationScheme2
    BS.empty
    xprv
    (word32fromWord31 ix)

deriveXPrvHard :: XPrv → Word31 → XPrv
deriveXPrvHard xprv ix =
  CC.deriveXPrv
    CC.DerivationScheme2
    BS.empty
    xprv
    (0x80000000 + word32fromWord31 ix)
#-}
