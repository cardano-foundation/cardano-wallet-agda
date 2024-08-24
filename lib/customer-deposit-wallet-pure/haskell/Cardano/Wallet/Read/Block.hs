{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Wallet.Read.Block
    ( Block
    , BlockNo (..)
    , RawHeaderHash
    , SlotNo (..)
    , getEraBHeader
    , getEraBlockNo
    , getEraHeaderHash
    , getEraSlotNo
    , getRawHeaderHash
    ) where

import Prelude

import Cardano.Wallet.Read.Eras
    ( IsEra
    )
import Numeric.Natural
    ( Natural
    )

newtype Block era = Block Natural

newtype HeaderHash era = HeaderHash Natural

newtype BHeader era = BHeader Natural

newtype SlotNo = SlotNo {unSlotNo :: Natural}
    deriving (Eq, Ord, Show)

newtype BlockNo = BlockNo {unBlockNo :: Natural}
    deriving (Eq, Ord, Show)

getEraSlotNo :: forall era. IsEra era => BHeader era -> SlotNo
getEraSlotNo = undefined

getEraBlockNo :: forall era. IsEra era => BHeader era -> BlockNo
getEraBlockNo = undefined

type RawHeaderHash = ()

getRawHeaderHash :: forall era. IsEra era => HeaderHash era -> RawHeaderHash
getRawHeaderHash = undefined

getEraHeaderHash :: forall era. IsEra era => Block era -> HeaderHash era
getEraHeaderHash = undefined

getEraBHeader :: forall era. IsEra era => Block era -> BHeader era
getEraBHeader = undefined
