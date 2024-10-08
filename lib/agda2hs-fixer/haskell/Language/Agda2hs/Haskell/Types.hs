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
    ) where

import Prelude

import Data.List
    ( foldl'
    )
import Data.Map
    ( Map
    )
import Language.Agda2hs.Agda.Types
    ( AgdaIdentifier
    )

import qualified Data.Char as Char
import qualified Data.Map.Strict as Map

{-----------------------------------------------------------------------------
    Haskell
------------------------------------------------------------------------------}
type HaskellIdentifier = String

-- | Line number
type LineNo = Int

type Line = String

-- | Source-level representation of a Haskell module.
data HaskellModule = HaskellModule
    { contents :: [Line]
        -- ^ Vanilla source code of the module
    , topLevelDeclarations :: Map HaskellIdentifier LineNo
        -- ^ Location of each top-level declaration.
    , comments :: Map HaskellIdentifier String
    }
    deriving (Eq, Show)

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

-- | Pretty print a Haskell module
prettyHaskellModule :: HaskellModule -> String
prettyHaskellModule m =
    unlines $
        prependLines
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
