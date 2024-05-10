{-# LANGUAGE StandaloneDeriving #-}
module Cardano.Wallet.Deposit.Read where

import qualified Haskell.Data.ByteString as BS (ByteString)
import Numeric.Natural (Natural)

-- Working around a limitation in agda2hs.
import Cardano.Wallet.Deposit.Read.Value
    ( Value
    )

type Addr = BS.ByteString

type Address = Addr

type TxId = BS.ByteString

type Ix = Int

type TxIn = (TxId, Ix)

data TxOut = TxOutC{address :: Address, value :: Value}

data TxBody = TxBodyC{inputs :: [TxIn], outputs :: [TxOut]}

data Tx = TxC{txid :: TxId, txbody :: TxBody}

type SlotNo = Natural

data WithOrigin a = Origin
                  | At a

deriving instance (Eq a) => Eq (WithOrigin a)

deriving instance (Ord a) => Ord (WithOrigin a)

type Slot = WithOrigin SlotNo

type BlockNo = Natural

type HashHeader = ()

type HashBBody = ()

data BHBody = BHBody{prev :: Maybe HashHeader, blockno :: BlockNo,
                     slot :: SlotNo, bhash :: HashBBody}

dummyBHBody :: BHBody
dummyBHBody = BHBody Nothing 128 42 ()

type Sig = ()

data BHeader = BHeader{blockHeaderBody :: BHBody,
                       blockHeaderSignature :: Sig}

bhHash :: BHeader -> HashHeader
bhHash _ = ()

dummyBHeader :: BHeader
dummyBHeader = BHeader dummyBHBody ()

data Block = Block{blockHeader :: BHeader, transactions :: [Tx]}

data ChainPoint = GenesisPoint
                | BlockPoint SlotNo HashHeader

chainPointFromBlock :: Block -> ChainPoint
chainPointFromBlock block
  = BlockPoint (slot (blockHeaderBody bh)) (bhHash bh)
  where
    bh :: BHeader
    bh = blockHeader block

