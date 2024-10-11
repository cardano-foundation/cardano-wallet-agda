{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Parser type.
-}
module Language.Agda2hs.Agda.Parser.Types
    ( Parser
    ) where

import Data.String (String)
import Data.Void (Void)
import Text.Megaparsec (Parsec)

type Parser = Parsec Void String
