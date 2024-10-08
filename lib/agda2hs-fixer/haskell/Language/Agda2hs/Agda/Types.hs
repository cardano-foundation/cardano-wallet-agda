{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Types for representing Agda modules.
-}
module Language.Agda2hs.Agda.Types
    ( AgdaIdentifier
    , AgdaDocumentation
    , DocString
    , DocItem (..)
    , TypeSignature
    , filterProperties
    ) where

import Prelude

import Data.List
    ( isPrefixOf
    )
import Data.Map
    ( Map
    )

import qualified Data.Map.Strict as Map

{-----------------------------------------------------------------------------
    Types
------------------------------------------------------------------------------}

type AgdaIdentifier = String

type AgdaDocumentation = Map AgdaIdentifier DocItem

type DocString = String

type TypeSignature = String

data DocItem = DocItem
    { identifier :: AgdaIdentifier
    -- ^ Name of the thing to be documented.
    , docString :: DocString
    -- ^ Documentation string (multiline)
    , typeSignature :: TypeSignature
    -- ^ Type signature of the thing to be documented (multiline).
    }

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}
-- | Keep those documentation items that are logical properties.
filterProperties :: AgdaDocumentation -> AgdaDocumentation
filterProperties = Map.filterWithKey isProperty

-- My naming convention for logical properties.
isProperty :: AgdaIdentifier -> DocItem -> Bool
isProperty name _ = "prop-" `isPrefixOf` name
