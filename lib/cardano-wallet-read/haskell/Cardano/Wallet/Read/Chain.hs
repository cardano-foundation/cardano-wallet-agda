{- |
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Data types relating to the consensus about the blockchain.
-}
module Cardano.Wallet.Read.Chain
    (
    -- * Points on the blockchain
    -- ** Slot
      WithOrigin (At, Origin)
    , Slot
    , slotFromChainPoint

    -- ** ChainPoint
    , ChainPoint (..)
    , getChainPoint
    , prettyChainPoint
    , chainPointFromChainTip

    -- ** ChainTip
    , ChainTip (..)
    , getChainTip
    , prettyChainTip
    ) where

import Cardano.Wallet.Read.Chain.Point
    ( ChainPoint (..)
    , ChainTip (..)
    , Slot
    , WithOrigin (At, Origin)
    , chainPointFromChainTip
    , getChainPoint
    , getChainTip
    , prettyChainPoint
    , prettyChainTip
    , slotFromChainPoint
    )
