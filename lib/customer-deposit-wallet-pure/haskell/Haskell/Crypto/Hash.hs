module Haskell.Crypto.Hash where

import Haskell.Data.ByteString (ByteString)

data Digest alg = DigestC ByteString

encodeDigest :: Digest alg -> ByteString
encodeDigest (DigestC d) = d

class HashAlgorithm alg where
    hash :: ByteString -> Digest alg

data TrivialHash = TrivialHashC

instance HashAlgorithm TrivialHash where
    hash = DigestC

