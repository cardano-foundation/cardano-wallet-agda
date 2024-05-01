{-# LANGUAGE UnicodeSyntax #-}

module Cardano.Wallet.Address.Hash where


import Cardano.Crypto.Hash
  ( Blake2b_224
  , Blake2b_256
  , HashAlgorithm (digest)
  )
import Data.ByteString
  ( ByteString
  )
import Data.Proxy
  ( Proxy (..)
  )

blake2b'224 :: ByteString ->ByteString
blake2b'224 = digest (Proxy :: Proxy Blake2b_224)

blake2b'256 :: ByteString ->ByteString
blake2b'256 = digest (Proxy :: Proxy Blake2b_256)

