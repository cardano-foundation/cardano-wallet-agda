{-# LANGUAGE UnicodeSyntax #-}

module Cardano.Wallet.Address.BIP32_Ed25519 where


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

-- FIXME: We define type synonyms here so that
-- they can be exported. Ideally, we would re-export from
-- the Cardano.Wallet.Crypto module.
type XPub = CC.XPub
type XPrv = CC.XPrv
type XSignature = CC.XSignature

toXPub :: XPrv ->XPub
toXPub = CC.toXPub

sign :: XPrv ->ByteString ->XSignature
sign = CC.sign BS.empty

verify :: XPub ->ByteString ->XSignature ->Bool
verify = CC.verify

word32fromWord31 :: Word31 ->Word32
word32fromWord31 = fromInteger . toInteger

deriveXPubSoft :: XPub ->Word31 ->XPub
deriveXPubSoft xpub ix =
  fromJust
    (CC.deriveXPub
      CC.DerivationScheme2
      xpub
      (word32fromWord31 ix)
    )
  -- deriveXPub always returns Just on Word31

deriveXPrvSoft :: XPrv ->Word31 ->XPrv
deriveXPrvSoft xprv ix =
  CC.deriveXPrv
    CC.DerivationScheme2
    BS.empty
    xprv
    (word32fromWord31 ix)

deriveXPrvHard :: XPrv ->Word31 ->XPrv
deriveXPrvHard xprv ix =
  CC.deriveXPrv
    CC.DerivationScheme2
    BS.empty
    xprv
    (0x80000000 + word32fromWord31 ix)

