{-# OPTIONS --erasure #-}
module Cardano.Wallet.Deposit.Read where

open import Haskell.Prelude

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
    Value
------------------------------------------------------------------------------}
data Value : Set where
    MkValue : Integer → Value

instance
  iSemigroupValue : Semigroup Value
  _<>_ {{iSemigroupValue}} (MkValue a) (MkValue b) = MkValue (a + b)

  iMonoidValue : Monoid Value
  iMonoidValue =
    record {DefaultMonoid (λ where .DefaultMonoid.mempty → MkValue 0)}

exceeds : Value → Value → Bool
exceeds (MkValue a) (MkValue b) = a >= b

minus : Value → Value → Value
minus (MkValue a) (MkValue b) = MkValue (a - b)

{-# COMPILE AGDA2HS Value #-}
{-# COMPILE AGDA2HS iSemigroupValue #-}
{-# COMPILE AGDA2HS iMonoidValue #-}
{-# COMPILE AGDA2HS exceeds #-}
{-# COMPILE AGDA2HS minus #-}

{-----------------------------------------------------------------------------
    Transactions
------------------------------------------------------------------------------}

TxId = BS.ByteString

instance
  iEqTxId : Eq TxId
  iEqTxId = BS.iEqByteString

  iOrdTxId : Ord TxId
  iOrdTxId = BS.iOrdByteString

  iLawfulEqTxId : IsLawfulEq TxId
  iLawfulEqTxId = BS.iLawfulEqByteString

Ix = Int

TxIn = TxId × Ix

record TxOut : Set where
  constructor TxOutC
  field
    address : Address
    value   : Value

open TxOut public

record TxBody : Set where
  constructor TxBodyC
  field
    inputs  : List TxIn
    outputs : List TxOut

open TxBody public

record Tx : Set where
  constructor TxC
  field
    txid   : TxId
    txbody : TxBody

open Tx public

{-# COMPILE AGDA2HS TxId #-}
{-# COMPILE AGDA2HS Ix #-}
{-# COMPILE AGDA2HS TxIn #-}
{-# COMPILE AGDA2HS TxOut #-}
{-# COMPILE AGDA2HS TxBody #-}
{-# COMPILE AGDA2HS Tx #-}

{-----------------------------------------------------------------------------
    Blocks
------------------------------------------------------------------------------}
BlockNo = Nat
Slot = Nat

{-# COMPILE AGDA2HS BlockNo #-}
{-# COMPILE AGDA2HS Slot #-}

HashHeader = ⊤
HashBBody = ⊤

{-# COMPILE AGDA2HS HashHeader #-}
{-# COMPILE AGDA2HS HashBBody #-}

record BHBody : Set where
  field
    prev    : Maybe HashHeader
    blockno : BlockNo
    slot    : Slot
    bhash   : HashBBody
open BHBody public

{-# COMPILE AGDA2HS BHBody #-}

dummyBHBody : BHBody
dummyBHBody = record
  { prev = Nothing
  ; blockno = 128
  ; slot = 42
  ; bhash = tt
  }

{-# COMPILE AGDA2HS dummyBHBody #-}

Sig = ⊤

{-# COMPILE AGDA2HS Sig #-}

record BHeader : Set where
  field
    blockHeaderBody      : BHBody
    blockHeaderSignature : Sig
open BHeader public

bhHash : BHeader → HashHeader
bhHash _ = tt

{-# COMPILE AGDA2HS bhHash #-}

-- postulate
-- bHeaderSize : BHeader → Nat

{-# COMPILE AGDA2HS BHeader #-}

dummyBHeader : BHeader
dummyBHeader = record
  { blockHeaderBody = dummyBHBody
  ; blockHeaderSignature = tt
  }

{-# COMPILE AGDA2HS dummyBHeader #-}

record Block : Set where
  field
    blockHeader  : BHeader
    transactions : List Tx
open Block public

{-# COMPILE AGDA2HS Block #-}

{-----------------------------------------------------------------------------
    ChainPoint
------------------------------------------------------------------------------}
data ChainPoint : Set where
  GenesisPoint : ChainPoint
  BlockPoint   : Slot → HashHeader → ChainPoint

{-# COMPILE AGDA2HS ChainPoint #-}

chainPointFromBlock : Block → ChainPoint
chainPointFromBlock block =
    BlockPoint (slot (blockHeaderBody bh)) (bhHash bh)
  where
    bh = blockHeader block

{-# COMPILE AGDA2HS chainPointFromBlock #-}
