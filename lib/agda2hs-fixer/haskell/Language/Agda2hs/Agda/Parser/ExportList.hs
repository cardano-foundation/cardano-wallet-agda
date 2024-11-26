{-# LANGUAGE OverloadedStrings #-}
{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Simple approximate parser for ad-hoc export lists.
-}
module Language.Agda2hs.Agda.Parser.ExportList
    ( ExportList
    , parseFileExportList
    ) where

import Prelude

import Language.Agda2hs.Agda.Parser.Lexer
    ( space
    , symbol
    )
import Language.Agda2hs.Agda.Parser.Types
    ( Parser
    )
import Language.Agda2hs.Agda.Types
    ( AgdaIdentifier
    , ExportItem (..)
    , ExportList
    , HeaderLevel (..)
    )
import Text.Megaparsec
    ( MonadParsec (takeWhileP)
    , (<|>)
    , empty
    , many
    , parse
    , satisfy
    , takeRest
    , sepBy
    , option
    , optional
    )

import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

{-----------------------------------------------------------------------------
    Parser functions
------------------------------------------------------------------------------}

parseFileExportList
    :: FilePath
        -- ^ Name of the file.
    -> String 
        -- ^ Contents of the file.
    -> Maybe (Maybe ExportList)
parseFileExportList filename file =
    case parse moduleFull filename file of
        Left _ -> Nothing
        Right x -> Just x

{-----------------------------------------------------------------------------
    Parser
------------------------------------------------------------------------------}
moduleFull :: Parser (Maybe ExportList)
moduleFull = space *> module'

module' :: Parser (Maybe ExportList)
module' = do
    _ <- symbol "module"
    _ <- moduleName
    es <- optional exportList
    _ <- symbol "where"
    _ <- takeRest
    pure es

exportList :: Parser ExportList
exportList = do
    _ <- symbolNoComments "{-|"
    s0 <- sectionHeaders
    ess <- optional semicolon *> (exportItems `sepBy` semicolon)
    _ <- symbolNoComments "-}"
    pure $ s0 <> concat ess
  where
    semicolon = symbolNoComments ";"

exportItems :: Parser [ExportItem]
exportItems = do
    before <- sectionHeaders
    identifier <- exportIdentifier
    after <- sectionHeaders
    pure $ before <> [identifier] <> after

exportIdentifier :: Parser ExportItem
exportIdentifier =
    ExportIdentifier <$> agdaNamePart <*> constructors
  where
    constructors = option False (True <$ symbolNoComments "(..)")

sectionHeaders :: Parser [ExportItem]
sectionHeaders =
    many (SectionHeader <$> headerLevel <*> line <* spaceNoComments)

headerLevel :: Parser HeaderLevel
headerLevel =
    (H3 <$ symbol' "-- ***")
    <|> (H2 <$ symbol' "-- **")
    <|> (H1 <$ symbol' "-- *")
  where
    symbol' = L.lexeme C.hspace1

{-----------------------------------------------------------------------------
    Lexer
------------------------------------------------------------------------------}
type ModuleName = String

moduleName :: Parser ModuleName
moduleName =
    L.lexeme space
        $ (:)
            <$> C.upperChar
            <*> many (C.alphaNumChar <|> satisfy (`elem` ['_','.']))

agdaNamePart :: Parser AgdaIdentifier
agdaNamePart =
    L.lexeme spaceNoComments
        $ (:)
            <$> satisfy (notForbidden ("'" <> forbiddenChars))
            <*> takeWhileP Nothing (notForbidden forbiddenChars)
  where
    notForbidden xs = not . (`elem` xs)

    forbiddenChars :: [Char]
    forbiddenChars = ".;{}()@ \n"

-- | Parse the rest of a line, without the newline character.
line :: Parser String
line = takeWhileP (Just "character") (/= '\n')

spaceNoComments :: Parser ()
spaceNoComments = L.space C.space1 empty empty

symbolNoComments :: String -> Parser String
symbolNoComments = L.symbol spaceNoComments
