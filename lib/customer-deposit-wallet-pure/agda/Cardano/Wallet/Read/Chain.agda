{-# OPTIONS --erasure #-}

-- Synchronized manually with the corresponding Haskell module.
module Cardano.Wallet.Read.Chain where

open import Haskell.Prelude
open import Cardano.Wallet.Read.Eras using
    ( IsEra
    )
open import Cardano.Wallet.Read.Block using
    ( Block
    ; BlockNo
    ; HeaderHash
    ; RawHeaderHash
    ; SlotNo
    )

import Cardano.Wallet.Read.Block as Block

{-----------------------------------------------------------------------------
    ChainTip
------------------------------------------------------------------------------}
data ChainTip : Set where
  GenesisTip : ChainTip
  BlockTip   : SlotNo → RawHeaderHash → BlockNo → ChainTip

instance
  iEqChainTip : Eq ChainTip
  iEqChainTip ._==_ GenesisTip GenesisTip = True
  iEqChainTip ._==_ (BlockTip x1 y1 z1) (BlockTip x2 y2 z2) =
    x1 == x2 && y1 == y2 && z1 == z2
  iEqChainTip ._==_ _      _      = False

getChainTip : ∀ {era} → {{IsEra era}} → Block era → ChainTip
getChainTip block =
    BlockTip
        (Block.getEraSlotNo (Block.getEraBHeader block))
        (Block.getRawHeaderHash (Block.getEraHeaderHash block))
        (Block.getEraBlockNo (Block.getEraBHeader block))

{-----------------------------------------------------------------------------
    ChainPoint
------------------------------------------------------------------------------}

-- | A point (block) on the Cardano blockchain.
data ChainPoint : Set where
  GenesisPoint : ChainPoint
  BlockPoint   : SlotNo → RawHeaderHash → ChainPoint

instance
  iEqChainPoint : Eq ChainPoint
  iEqChainPoint ._==_ GenesisPoint GenesisPoint = True
  iEqChainPoint ._==_ (BlockPoint x1 y1) (BlockPoint x2 y2) =
    x1 == x2 && y1 == y2
  iEqChainPoint ._==_ _      _      = False

chainPointFromChainTip : ChainTip → ChainPoint
chainPointFromChainTip GenesisTip = GenesisPoint
chainPointFromChainTip (BlockTip slot hash _) = BlockPoint slot hash

getChainPoint : ∀ {era} → {{IsEra era}} → Block era → ChainPoint
getChainPoint block =
    BlockPoint
        (Block.getEraSlotNo (Block.getEraBHeader block))
        (Block.getRawHeaderHash (Block.getEraHeaderHash block))
