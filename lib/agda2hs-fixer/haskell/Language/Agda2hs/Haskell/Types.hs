{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Types for representing Haskell modules.
-}
module Language.Agda2hs.Haskell.Types
    ( HaskellModule (..)
    , prettyHaskellModule

    , Line
    , LineNo
    , prependHaddockLines
    , appendHaddockNamedChunks
    , appendHaddockSection

    , HaskellIdentifier
    , fromAgdaIdentifier
    , completeExportsWithInternals
    ) where

import Prelude

import Data.List
    ( foldl'
    , isPrefixOf
    , isSuffixOf
    )
import Data.Map
    ( Map
    )
import Data.Maybe
    ( fromMaybe
    )
import Language.Agda2hs.Agda.Types
    ( AgdaIdentifier
    , ExportList
    , ExportItem (..)
    , HeaderLevel (..)
    , collectIdentifiers
    , isProperty
    )

import qualified Data.Char as Char
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

{-----------------------------------------------------------------------------
    Types
------------------------------------------------------------------------------}
type HaskellIdentifier = String

-- | Line number
type LineNo = Int

type Line = String

-- | Source-level representation of a Haskell module.
data HaskellModule = HaskellModule
    { contents :: [Line]
        -- ^ Original source code of the module.
    , topLevelDeclarations :: Map HaskellIdentifier LineNo
        -- ^ Location of each top-level declaration.
    , exportList :: Maybe ExportList
        -- ^ Export list to be added to the module.
    , comments :: Map HaskellIdentifier String
        -- ^ Comments to be added before each identifier.
    }
    deriving (Eq, Show)

{-----------------------------------------------------------------------------
    Haddock documentation
------------------------------------------------------------------------------}
-- | Prepend multiline Haddock comments before every given identifier.
prependHaddockLines
    :: Map HaskellIdentifier [String]
    -> HaskellModule
    -> HaskellModule
prependHaddockLines haddocks m = m
    { comments =
        Map.unionWith (<>) (Map.map unlines haddocks) (comments m)
    }

-- | Append a Haddock section title.
appendHaddockSection
    :: String
    -> HaskellModule
    -> HaskellModule
appendHaddockSection title m =
    m { contents = contents m <> ["-- * " <> title]}

-- | Append named chunks of Haddock documentation.
appendHaddockNamedChunks
    :: Map String [Line]
    -> HaskellModule
    -> HaskellModule
appendHaddockNamedChunks chunks m = m
    { contents =
        contents m
            <> mconcat (map renderNamedChunk $ Map.toList chunks)
    }
  where
    renderNamedChunk (name, chunk) =
        ["{- $" <> name] <> chunk <> ["-}"]

{-----------------------------------------------------------------------------
    Export lists
------------------------------------------------------------------------------}
-- | Fill an export list with all internal definitions.
--
-- FIXME: Currently does not export constructors and fields for
-- data types correctly.
completeExportsWithInternals :: HaskellModule -> HaskellModule
completeExportsWithInternals m
    | not (Set.null internals) = m
        { exportList = Just $
            exports
            <> [SectionHeader H1 "Internal"]
            <> Set.toList
                (Set.map (\name -> ExportIdentifier name False) internals)
        }
    | otherwise = m
  where
    exports = fromMaybe [] (exportList m)
    internals =
        Set.difference
            (Map.keysSet (topLevelDeclarations m))
            (collectIdentifiers exports)

{-----------------------------------------------------------------------------
    Pretty printing and rendering
------------------------------------------------------------------------------}

-- | Pretty print a Haskell module
prettyHaskellModule :: HaskellModule -> String
prettyHaskellModule m =
    unlines
    $ replaceExportList (exportList m)
    $ prependLines
            (contents m)
            (joinMaps
                (topLevelDeclarations m)
                (Map.map mkHaddock $ comments m)
            )
  where
    mkHaddock s = "{-|\n" <> s <> "-}\n"

joinMaps
    :: forall key a. Ord key
    => Map key LineNo -> Map key a -> Map LineNo a
joinMaps xs ys =
    foldl' insert Map.empty (Map.toList xs)
  where
    insert :: Map LineNo a -> (key, LineNo) -> Map LineNo a
    insert m (key,ix) =
        case Map.lookup key ys of
            Just y -> Map.insert ix y m
            Nothing -> m

prependLines :: Semigroup a => [a] -> Map LineNo a -> [a]
prependLines original0 inserted = both
  where
    original = Map.fromList $ zip [0..] original0
    both = Map.elems $ Map.unionWith (\x y -> x <> y) inserted original

-- | Replace the export list of a Haskell module given in source form.
--
-- Assumes that the module name is on a single line of the form
--   @module Module.Name where@
replaceExportList
    :: Maybe ExportList -> [Line] -> [Line]
replaceExportList Nothing fileLines = fileLines
replaceExportList (Just exports) fileLines =
    foldMap replaceModuleDeclaration m
  where
    m = Map.fromList $ zip [0 :: Int ..] fileLines

    replaceModuleDeclaration line
        | "module" `isPrefixOf` line && "where" `isSuffixOf` line =
            [dropWhere line]
            <> indent 4 (renderExportList exports <> ["where"])
        | otherwise = [line]

    dropWhere = reverse . drop (length ("where" :: String)) . reverse

-- | Render an export list as individual lines
renderExportList :: ExportList -> [Line]
renderExportList xs =
    ["("] <> dropLastComma (concat $ map renderExportItem xs) <> [")"]
  where
    renderExportItem :: ExportItem -> [Line]
    renderExportItem (ExportIdentifier agdaName doConstructors)
        | Just hsName <- fromAgdaIdentifier agdaName =
            [hsName <> (if doConstructors then " (..)" else "") <> ","]
        | isProperty agdaName =
            ["-- $" <> agdaName, ""]
    renderExportItem (SectionHeader headerLevel text) =
        [renderHeaderLevel headerLevel <> " " <> text]
    renderExportItem _ = []

dropLastComma :: [Line] -> [Line]
dropLastComma = reverse . onHead dropComma . reverse
  where
    dropComma [] = []
    dropComma (',':xs) = xs
    dropComma (x:xs) = x:xs

    onHead _ [] = []
    onHead f (x:xs) = f x : xs

renderHeaderLevel :: HeaderLevel -> String
renderHeaderLevel H1 = "-- *"
renderHeaderLevel H2 = "-- **"
renderHeaderLevel H3 = "-- ***"

indent :: Int -> [Line] -> [Line]
indent n = map (replicate n ' ' <>)

{-----------------------------------------------------------------------------
    Agda to Haskell
------------------------------------------------------------------------------}
-- | Attempt to convert an identifier in Agda to a Haskell identifier.
--
-- Works for both values (starts with lowercase)
-- and types (starts with uppercase).
fromAgdaIdentifier :: AgdaIdentifier -> Maybe HaskellIdentifier
fromAgdaIdentifier [] = Nothing
fromAgdaIdentifier "_" = Nothing
fromAgdaIdentifier s@(x:xs)
    | validStart x && all valid xs = Just s
    | otherwise = Nothing
  where
    validStart c = small c || large c
    valid c = small c || large c || digit c || tick c
    small c = Char.isLowerCase c || c == '_'
    large = Char.isUpperCase
    digit = Char.isDigit
    tick = (== '\'')
