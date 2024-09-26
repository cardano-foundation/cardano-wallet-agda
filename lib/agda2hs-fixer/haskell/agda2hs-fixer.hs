{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Main module.
-}
module Main where

import Prelude

import Control.Monad
    ( when
    )
import Language.Agda2hs.Documentation
    ( modifyFileAddingDocumentation
    )
import Main.Utf8
    ( withUtf8
    )
import System.Directory
    ( doesFileExist
    )
import System.FilePath
    ( joinPath
    , replaceExtension
    , splitPath
    )
import System.Environment
    ( getArgs
    )

{-----------------------------------------------------------------------------
    Main function
------------------------------------------------------------------------------}
main :: IO ()
main = withUtf8 $ do
    files <- getArgs
    mapM_ fixupHaskell files

{-----------------------------------------------------------------------------
    Fixup
------------------------------------------------------------------------------}
-- | Fix up a compiled @.hs@ file.
fixupHaskell :: FilePath -> IO ()
fixupHaskell haskellFilePath = do
    putStrLn $ "Fixing " <> haskellFilePath
    b <- doesFileExist agdaFilePath
    when b
        $ modifyFileAddingDocumentation agdaFilePath haskellFilePath
  where
    agdaFilePath =
        flip replaceExtension ".agda"
        . joinPath
        . ([".", "agda"] <>)
        . drop 2 -- drops prefix  ./haskell/
        $ splitPath haskellFilePath
