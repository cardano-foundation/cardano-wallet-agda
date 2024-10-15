{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Somewhat incorrect parser for Haskell.
-}
module Language.Agda2hs.Haskell.Parser
    ( parseFileHaskellModule
    ) where

import Prelude

import Data.Map
    ( Map
    )
import Language.Agda2hs.Haskell.Types
    ( HaskellIdentifier
    , HaskellModule (..)
    , LineNo
    )

import qualified Data.Map.Strict as Map
import qualified Language.Haskell.Exts as Hs

{-----------------------------------------------------------------------------
    Parser
------------------------------------------------------------------------------}
parseFileHaskellModule
    :: FilePath
        -- ^ Name of the file.
    -> String 
        -- ^ Contents of the file.
    -> Maybe HaskellModule
parseFileHaskellModule filename file =
    case parseResult of
        Hs.ParseOk res -> Just $ mkHaskellModule res
        Hs.ParseFailed _sloc _msg -> Nothing
  where
    parseResult =
        Hs.parseFileContentsWithMode
            (Hs.defaultParseMode{ Hs.parseFilename = filename })
            file

    mkHaskellModule parsedModule = 
        HaskellModule
        { contents = lines file
        , topLevelDeclarations = collectTopLevelDeclarations parsedModule
        , exportList = Nothing
        , comments = Map.empty
        }

collectTopLevelDeclarations
    :: Hs.Module Hs.SrcSpanInfo
    -> Map HaskellIdentifier LineNo
collectTopLevelDeclarations = Map.fromList . fromModule
  where
    fromModule (Hs.Module _ _ _ _ decls) = concatMap fromDeclaration decls
    fromModule _ = []

    fromDeclaration (Hs.TypeSig _ (name:_) _) = fromName name
    fromDeclaration (Hs.TypeDecl _ x _) = fromDeclHead x
    fromDeclaration (Hs.DataDecl _ _ _ x _ _) = fromDeclHead x
    fromDeclaration _ = []

    fromName (Hs.Ident info s) = [(s, Hs.startLine info - 1)]
    fromName _ = []

    fromDeclHead (Hs.DHead _ name) = fromName name
    fromDeclHead (Hs.DHInfix _ _ name) = fromName name
    fromDeclHead (Hs.DHParen _ x) = fromDeclHead x
    fromDeclHead (Hs.DHApp _ x _) = fromDeclHead x
