{-# LANGUAGE StandaloneDeriving #-}

module Cardano.Wallet.Deposit.Read where

import Cardano.Wallet.Read.Block (Block, SlotNo)
import Cardano.Wallet.Read.Chain
    ( ChainPoint (BlockPoint, GenesisPoint)
    , getChainPoint
    )
import Cardano.Wallet.Read.Eras (IsEra)
import Cardano.Wallet.Read.Tx (Tx, TxIn, TxOut)
import qualified Haskell.Data.ByteString as BS (ByteString)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read.Value
    ( Value
    )

type Addr = BS.ByteString

type Address = Addr

data TxBody = TxBodyC {inputs :: [TxIn], outputs :: [TxOut]}

data WithOrigin a
    = Origin
    | At a

deriving instance (Eq a) => Eq (WithOrigin a)

deriving instance (Ord a) => Ord (WithOrigin a)

type Slot = WithOrigin SlotNo

getEraTransactions :: IsEra era => Block era -> [Tx era]
getEraTransactions block = []

chainPointFromBlock :: IsEra era => Block era -> ChainPoint
chainPointFromBlock = getChainPoint

slotFromChainPoint :: ChainPoint -> Slot
slotFromChainPoint GenesisPoint = Origin
slotFromChainPoint (BlockPoint slotNo _) = At slotNo
