-- |
-- Copyright: © 2025 Cardano Foundation
-- License: Apache-2.0
--
-- Cryptographic hash functions with monomorphic types.
module Cardano.Crypto.Hash.Monomorphic
    ( blake2b'224
    , blake2b'256
    )
where

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

-- | Compute the
-- [BLAKE2b](https://en.wikipedia.org/wiki/BLAKE_%28hash_function%29%23BLAKE2b_algorithm)
-- hash of the input bytes
-- with a 224 bit (28 bytes) digest.
blake2b'224 :: ByteString -> ByteString
blake2b'224 = digest (Proxy :: Proxy Blake2b_224)

-- | Compute the
-- [BLAKE2b](https://en.wikipedia.org/wiki/BLAKE_%28hash_function%29%23BLAKE2b_algorithm)
-- hash of the input bytes
-- with a 256 bit (32 bytes) digest.
blake2b'256 :: ByteString -> ByteString
blake2b'256 = digest (Proxy :: Proxy Blake2b_256)
