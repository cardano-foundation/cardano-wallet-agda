{-# LANGUAGE StandaloneDeriving #-}
module Cardano.Wallet.Address.BIP32 where

import Data.Word.Odd (Word31)

data DerivationType = Soft
                    | Hardened

deriving instance Eq DerivationType

deriving instance Ord DerivationType

data BIP32Path = Root
               | Segment BIP32Path DerivationType Word31

deriving instance Eq BIP32Path

deriving instance Ord BIP32Path

