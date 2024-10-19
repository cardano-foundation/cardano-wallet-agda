{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Types for representing Agda modules.
-}
module Language.Agda2hs.Agda.Types
    ( -- * Identifiers
      AgdaIdentifier
    , TypeSignature
    , isProperty

    -- * Documentation
    , AgdaDocumentation
    , filterProperties
    , DocString
    , DocItem (..)

    -- * Export lists
    , ExportList
    , ExportItem (..)
    , ExportConstructors
    , HeaderLevel (..)
    , collectIdentifiers
    ) where

import Prelude

import Data.List
    ( isPrefixOf
    )
import Data.Map
    ( Map
    )
import Data.Set
    ( Set
    )

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

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
    } deriving (Eq, Ord, Show)

type ExportConstructors = Bool

data HeaderLevel = H1 | H2 | H3
    deriving (Eq, Ord, Show)

data ExportItem
    = ExportIdentifier AgdaIdentifier ExportConstructors
    | SectionHeader HeaderLevel String
    deriving (Eq, Ord, Show)

type ExportList = [ExportItem]

{-----------------------------------------------------------------------------
    Operations
------------------------------------------------------------------------------}
-- | Keep those documentation items that are logical properties.
filterProperties :: AgdaDocumentation -> AgdaDocumentation
filterProperties = Map.filterWithKey (const . isProperty)

-- | My naming convention for logical properties.
isProperty :: AgdaIdentifier -> Bool
isProperty name = "prop-" `isPrefixOf` name

collectIdentifiers :: ExportList -> Set AgdaIdentifier
collectIdentifiers xs = Set.fromList [name | ExportIdentifier name _ <- xs ]
