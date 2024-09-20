{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Main module.
-}
module Main where

import Prelude

import Main.Utf8
    ( withUtf8
    )

main :: IO ()
main = withUtf8 $ putStrLn "Gimme, gimme Agda after midnight!"
