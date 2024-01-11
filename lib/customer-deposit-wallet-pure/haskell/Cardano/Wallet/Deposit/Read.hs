module Cardano.Wallet.Deposit.Read where

import qualified Haskell.Data.ByteString as BS (ByteString)
import Numeric.Natural (Natural)

type Addr = BS.ByteString

type Address = Addr

type Slot = Natural

data Value = MkValue Integer

instance Semigroup Value where
    MkValue a <> MkValue b = MkValue (a + b)

instance Monoid Value where
    mempty = MkValue 0

exceeds :: Value -> Value -> Bool
exceeds (MkValue a) (MkValue b) = a >= b

minus :: Value -> Value -> Value
minus (MkValue a) (MkValue b) = MkValue (a - b)

type TxId = Natural

type Ix = Int

type TxIn = (TxId, Ix)

data TxOut = TxOutC{address :: Address, value :: Value}

data Tx = TxC{txid :: TxId, inputs :: [TxIn], outputs :: [TxOut]}

