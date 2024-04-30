{-# OPTIONS --erasure #-}

module Cardano.Wallet.Address.BIP32_Ed25519 where

open import Haskell.Prelude

open import Haskell.Data.ByteString using
  ( ByteString
  )
open import Haskell.Data.Word.Odd using
  ( Word31
  )

{-# FOREIGN AGDA2HS
{-# LANGUAGE UnicodeSyntax #-}
import Cardano.Crypto.Wallet
  ( XPrv
  , XPub
  , XSignature
  , toXPub
  )
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
sign :: XPrv → ByteString → XSignature
sign = CC.sign BS.empty

verify :: XPub → ByteString → XSignature → Bool
verify = CC.verify
#-}

{-----------------------------------------------------------------------------
    Key derivation
------------------------------------------------------------------------------}

postulate
  deriveXPubSoft : XPub → Word31 → XPub
  deriveXPrvSoft : XPrv → Word31 → XPrv
  deriveXPrvHard : XPrv → Word31 → XPrv

  prop-derive-soft
    : ∀ (xprv : XPrv)
        (ix   : Word31)
    → deriveXPubSoft (toXPub xprv) ix
      ≡ toXPub (deriveXPrvSoft xprv ix)

  -- The following properties about injectivity
  -- are not true in the strict sense,
  -- only cryptographically hard.
  prop-deriveXPubSoft-injective
    : ∀ (xpub    : XPub)
        (ix1 ix2 : Word31)
    → deriveXPubSoft xpub ix1 ≡ deriveXPubSoft xpub ix2
    → ix1 ≡ ix2

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
