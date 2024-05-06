module Cardano.Wallet.Address.BIP32 where

import Data.Word.Odd (Word31)

data DerivationType = Soft
                    | Hardened

data BIP32Path = Root
               | Segment BIP32Path DerivationType Word31

