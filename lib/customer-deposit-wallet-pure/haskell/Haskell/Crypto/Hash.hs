module Haskell.Crypto.Hash where

import Haskell.Data.ByteString (ByteString)
import Numeric.Natural (Natural)

data Digest alg = DigestC Natural

encodeDigest :: Digest alg -> Natural
encodeDigest (DigestC n) = n

class HashAlgorithm alg where
    hash :: ByteString -> Digest alg

data TrivialHash = TrivialHashC

instance HashAlgorithm TrivialHash where
    hash = \ _ -> DigestC 0

