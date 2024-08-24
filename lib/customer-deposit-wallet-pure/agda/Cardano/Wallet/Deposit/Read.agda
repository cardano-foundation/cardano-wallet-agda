{-# OPTIONS --erasure #-}
module Cardano.Wallet.Deposit.Read where

open import Haskell.Prelude

open import Cardano.Wallet.Read.Eras public
open import Cardano.Wallet.Read.Block public
open import Cardano.Wallet.Read.Chain public
open import Cardano.Wallet.Read.Tx public
open import Cardano.Wallet.Read.Value public

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Cardano.Wallet.Read.Value 
    ( Value
    )
#-}

import Haskell.Data.ByteString as BS
import Haskell.Data.Map as Map

{-----------------------------------------------------------------------------
    Address
------------------------------------------------------------------------------}

Addr = BS.ByteString
Address = Addr

instance
  iEqAddress : Eq Address
  iEqAddress = BS.iEqByteString

  iOrdAddress : Ord Address
  iOrdAddress = BS.iOrdByteString

  iLawfulEqAddress : IsLawfulEq Address
  iLawfulEqAddress = BS.iLawfulEqByteString

{-# COMPILE AGDA2HS Addr #-}
{-# COMPILE AGDA2HS Address #-}

{-----------------------------------------------------------------------------
    Transactions
------------------------------------------------------------------------------}

record TxBody : Set where
  constructor TxBodyC
  field
    inputs  : List TxIn
    outputs : List TxOut

open TxBody public

{-# COMPILE AGDA2HS TxBody #-}

{-----------------------------------------------------------------------------
    Slot
------------------------------------------------------------------------------}

data WithOrigin (a : Set) : Set where
  Origin : WithOrigin a
  At     : a → WithOrigin a

instance
  iEqWithOrigin : {{Eq a}} → Eq (WithOrigin a)
  iEqWithOrigin ._==_ Origin Origin = True
  iEqWithOrigin ._==_ (At x) (At y) = x == y
  iEqWithOrigin ._==_ _      _      = False

  iOrdWithOrigin : {{Ord a}} → Ord (WithOrigin a)
  iOrdWithOrigin = ordFromCompare λ where
    Origin Origin → EQ
    Origin (At _) → LT
    (At _) Origin → GT
    (At x) (At y) → compare x y

{-# COMPILE AGDA2HS WithOrigin #-}
{-# COMPILE AGDA2HS iEqWithOrigin derive #-}
{-# COMPILE AGDA2HS iOrdWithOrigin derive #-}

Slot : Set
Slot = WithOrigin SlotNo

{-# COMPILE AGDA2HS Slot #-}

{-----------------------------------------------------------------------------
    Block
------------------------------------------------------------------------------}
getEraTransactions : {{IsEra era}} → Block era → List (Tx era)
getEraTransactions block = []

{-# COMPILE AGDA2HS getEraTransactions #-}

{-----------------------------------------------------------------------------
    ChainPoint
------------------------------------------------------------------------------}

chainPointFromBlock : {{IsEra era}} → Block era → ChainPoint
chainPointFromBlock = getChainPoint

{-# COMPILE AGDA2HS chainPointFromBlock #-}

slotFromChainPoint : ChainPoint → Slot
slotFromChainPoint GenesisPoint = WithOrigin.Origin
slotFromChainPoint (BlockPoint slotNo _) = WithOrigin.At slotNo

{-# COMPILE AGDA2HS slotFromChainPoint #-}