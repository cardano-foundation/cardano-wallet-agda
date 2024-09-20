{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Types for representing Agda modules.
-}
module Language.Agda2hs.Agda.Types
    ( AgdaIdentifier
    , AgdaDocumentation
    , DocString
    ) where

import Prelude

import Data.Map
    ( Map
    )

{-----------------------------------------------------------------------------
    Agda
------------------------------------------------------------------------------}
type AgdaIdentifier = String

type AgdaDocumentation = Map AgdaIdentifier DocString

type DocString = String
