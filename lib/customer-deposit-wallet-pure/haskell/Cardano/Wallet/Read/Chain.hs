{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoFieldSelectors #-}

-- |
-- Copyright: © 2024 Cardano Foundation
-- License: Apache-2.0
--
-- Data types relating to the consensus about the blockchain.
module Cardano.Wallet.Read.Chain
    ( -- * ChainPoint
      ChainPoint (..)
    , getChainPoint
    , chainPointFromChainTip

      -- * ChainTip
    , ChainTip (..)
    , getChainTip
    ) where

import Prelude

import Cardano.Wallet.Read.Block
    ( Block
    , BlockNo (..)
    , RawHeaderHash
    , SlotNo (..)
    , getEraBHeader
    , getEraBlockNo
    , getEraHeaderHash
    , getEraSlotNo
    , getRawHeaderHash
    )
import Cardano.Wallet.Read.Eras
    ( IsEra
    )
import GHC.Generics
    ( Generic
    )

{-----------------------------------------------------------------------------
    ChainPoint
------------------------------------------------------------------------------}

-- | A point (block) on the Cardano blockchain.
data ChainPoint
    = GenesisPoint
    | BlockPoint
        { slotNo :: !SlotNo
        , headerHash :: !RawHeaderHash
        }
    deriving (Eq, Ord, Show, Generic)

{-# INLINEABLE getChainPoint #-}
getChainPoint :: IsEra era => Block era -> ChainPoint
getChainPoint block =
    BlockPoint
        { slotNo = getEraSlotNo $ getEraBHeader block
        , headerHash = getRawHeaderHash $ getEraHeaderHash block
        }

chainPointFromChainTip :: ChainTip -> ChainPoint
chainPointFromChainTip GenesisTip = GenesisPoint
chainPointFromChainTip (BlockTip slot hash _) = BlockPoint slot hash

{-----------------------------------------------------------------------------
    Tip
------------------------------------------------------------------------------}

-- | Used in chain-sync protocol to advertise the tip of the server's chain.
-- Records the 'ChainPoint' and the 'BlockNo' of the block.
data ChainTip
    = GenesisTip
    | BlockTip
        { slotNo :: !SlotNo
        , headerHash :: !RawHeaderHash
        , blockNo :: !BlockNo
        }
    deriving (Eq, Ord, Show, Generic)

{-# INLINEABLE getChainTip #-}
getChainTip :: IsEra era => Block era -> ChainTip
getChainTip block =
    BlockTip
        { slotNo = getEraSlotNo $ getEraBHeader block
        , headerHash = getRawHeaderHash $ getEraHeaderHash block
        , blockNo = getEraBlockNo $ getEraBHeader block
        }
