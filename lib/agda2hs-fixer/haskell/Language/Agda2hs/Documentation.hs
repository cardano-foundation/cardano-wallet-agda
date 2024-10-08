{-# LANGUAGE ScopedTypeVariables #-}
{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Add Haddock comments to `.hs` file generated from `.agda` file.
-}
module Language.Agda2hs.Documentation
    ( modifyFileAddingDocumentation
    ) where

import Prelude

import Control.Exception
    ( Exception
    , catch
    , throw
    )
import Language.Agda2hs.Agda.Parser
    ( parseFileAgdaDocumentation
    )
import Language.Agda2hs.Agda.Types
    ( AgdaDocumentation
    , DocItem (..)
    , filterProperties
    )
import Language.Agda2hs.Haskell.Parser
    ( parseFileHaskellModule
    )
import Language.Agda2hs.Haskell.Types
    ( HaskellModule
    , Line
    , appendHaddockNamedChunks
    , appendHaddockSection
    , prependHaddockLines
    , prettyHaskellModule
    )
import System.IO
    ( hPutStrLn
    , readFile'
    , stderr
    )

import qualified Data.Map.Strict as Map

{-----------------------------------------------------------------------------
    Parser
------------------------------------------------------------------------------}
data ErrParseError
    = ErrParseErrorAgda FilePath
    | ErrParseErrorHaskell FilePath
    deriving (Eq, Show)

instance Exception ErrParseError

-- | Modify a `.hs` file that was autogenerated from `.agda` to include
-- Haddock comments.
modifyFileAddingDocumentation
    :: FilePath
        -- ^ Agda file.
    -> FilePath
        -- ^ Generated Haskell file to add documentation to.
    -> IO ()
modifyFileAddingDocumentation agdaPath haskellPath = do
    doModify `catch` (\(e :: ErrParseError) -> warning $ show e)
  where
    warning s = hPutStrLn stderr $ "Warning: " ++ s

    doModify = do
        agdaCode <- readFile agdaPath
        agdaDoc <-
            maybe (throw $ ErrParseErrorAgda agdaPath) pure
                $ parseFileAgdaDocumentation agdaPath agdaCode

        haskellCode <- readFile' haskellPath
        haskell0 <-
            maybe (throw $ ErrParseErrorHaskell haskellPath) pure
                $ parseFileHaskellModule haskellPath haskellCode

        let haskell1 = patchAgdaDocumentation agdaDoc haskell0

--        putStrLn $ prettyHaskellModule haskell1
        writeFile haskellPath $ prettyHaskellModule haskell1

-- | Add documentation from the .agda module to a generated .hs module.
patchAgdaDocumentation
    :: AgdaDocumentation -> HaskellModule -> HaskellModule
patchAgdaDocumentation agdaDoc =
    appendHaddockNamedChunks (Map.map renderAgdaProperty agdaProperties)
    . (if Map.null agdaProperties then id else appendHaddockSection "Properties")
    . prependHaddockLines (Map.map (lines . docString) agdaDoc)
  where
    agdaProperties = filterProperties agdaDoc

renderAgdaProperty :: DocItem -> [Line]
renderAgdaProperty doc =
    [prettyAnchor, newline, "[" <> identifier doc <> "]:"]
    <> indent 4 (dropNewLinesAtEnd prettyDoc <> [newline] <> prettyType)
  where
    prettyAnchor = "#" <> identifier doc <> "#"
    prettyDoc = lines (docString doc)
    prettyType = ["@"] <> lines (typeSignature doc) <> ["@"]
 
dropNewLinesAtEnd :: [Line] -> [Line]
dropNewLinesAtEnd = reverse . dropWhile (== newline) . reverse

newline :: Line
newline = ""

indent :: Int -> [Line] -> [Line]
indent n = map (replicate n ' ' <>)
