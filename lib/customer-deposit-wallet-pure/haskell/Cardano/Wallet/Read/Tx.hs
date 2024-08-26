{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Wallet.Read.Tx
    ( TxId
    , TxIx
    , TxIn
    , TxOut
    , mkBasicTxOut
    , getCompactAddr
    , getValue
    , utxoFromEraTx
    , Tx
    , getTxId
    , getInputs
    ) where

import Prelude

import Cardano.Wallet.Read.Address
    ( CompactAddr
    )
import Cardano.Wallet.Read.Eras
    ( IsEra
    )
import Cardano.Wallet.Read.Value
    ( Value
    )
import Data.ByteString
    ( ByteString
    )
import Data.Map
    ( Map
    )
import Data.Set
    ( Set
    )
import Data.Word
    ( Word16
    )

{-----------------------------------------------------------------------------
    TxId
------------------------------------------------------------------------------}
newtype TxId = TxId ByteString
    deriving (Eq, Ord)

{-----------------------------------------------------------------------------
    TxIx
------------------------------------------------------------------------------}
newtype TxIx = TxIxC {word16FromTxIx :: Word16}
    deriving (Eq, Ord)

{-----------------------------------------------------------------------------
    TxIn
------------------------------------------------------------------------------}
data TxIn = TxInC
    { inputId :: TxId
    , inputIx :: TxIx
    }
    deriving (Eq, Ord)

{-----------------------------------------------------------------------------
    TxOut
------------------------------------------------------------------------------}
data TxOut = TxOutC
    { getCompactAddr :: CompactAddr
    , getValue :: Value
    }

mkBasicTxOut :: CompactAddr -> Value -> TxOut
mkBasicTxOut = TxOutC

{-----------------------------------------------------------------------------
    Tx
------------------------------------------------------------------------------}
data Tx era = Tx

getTxId :: forall era. IsEra era => Tx era -> TxId
getTxId = undefined

utxoFromEraTx :: forall era. IsEra era => Tx era -> Map TxIn TxOut
utxoFromEraTx = undefined

getInputs :: forall era. IsEra era => Tx era -> Set TxIn
getInputs = undefined
