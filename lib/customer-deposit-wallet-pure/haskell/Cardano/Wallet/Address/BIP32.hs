{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Address.BIP32 where

import Data.Word.Odd (Word31)
import Prelude hiding (null, subtract)

-- |
-- Method for deriving child keys.
data DerivationType
    = Soft
    | Hardened

deriving instance Eq DerivationType

deriving instance Ord DerivationType

-- |
-- An absolute path according to the
-- [BIP-32](https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki) standard.
--
-- Example:
-- The example notated in the standard as
--
-- > m/3H/2/5
--
-- corresponds to the value
--
-- > Segment (Segment (Segment Root Hardened 3) Soft 2) Soft 5
data BIP32Path
    = Root
    | Segment BIP32Path DerivationType Word31

deriving instance Eq BIP32Path

deriving instance Ord BIP32Path
