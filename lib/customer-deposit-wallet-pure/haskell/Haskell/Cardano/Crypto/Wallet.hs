{-# LANGUAGE UnicodeSyntax #-}

module Haskell.Cardano.Crypto.Wallet
    ( module Cardano.Crypto.Wallet
    , xPrvChangePass
    , deriveXPrv
    , deriveXPub
    , sign
    , verify
    , word32fromWord31Low
    , word32fromWord31High
    ) where

import Cardano.Crypto.Wallet hiding
    ( deriveXPrv
    , deriveXPub
    , sign
    , verify
    , xPrvChangePass
    )
import Data.ByteString
    ( ByteString
    )
import Data.Word
    ( Word32
    )
import Data.Word.Odd
    ( Word31
    )

import qualified Cardano.Crypto.Wallet as CC

-- | Convert 'Word31' into 'Word32' with highest bit @0@.
word32fromWord31Low :: Word31 -> Word32
word32fromWord31Low = fromInteger . toInteger

-- | Convert 'Word31' into 'Word32' with highest bit @1@.
word32fromWord31High :: Word31 -> Word32
word32fromWord31High w = 0x80000000 + word32fromWord31Low w

xPrvChangePass :: ByteString -> ByteString -> XPrv -> XPrv
xPrvChangePass = CC.xPrvChangePass

deriveXPrv :: DerivationScheme -> ByteString -> XPrv -> Word32 -> XPrv
deriveXPrv = CC.deriveXPrv

deriveXPub :: DerivationScheme -> XPub -> Word32 -> Maybe XPub
deriveXPub = CC.deriveXPub

sign :: ByteString -> XPrv -> ByteString -> XSignature
sign = CC.sign

verify :: XPub -> ByteString -> XSignature -> Bool
verify = CC.verify
