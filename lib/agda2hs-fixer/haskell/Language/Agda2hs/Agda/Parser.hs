{-|
Copyright: © 2024 Cardano Foundation
License: Apache-2.0

Simple, somewhat incorrect parser for documentation comments.
-}
module Language.Agda2hs.Agda.Parser
    ( AgdaDocumentation
    , parseFileAgdaDocumentation
    ) where

import Prelude

import Data.Void
    ( Void
    )
import Language.Agda2hs.Agda.Types
    ( AgdaIdentifier
    , AgdaDocumentation
    , DocString
    )
import Text.Megaparsec
    ( MonadParsec (notFollowedBy, takeWhileP, try)
    , Parsec
    , (<|>)
    , anySingle
    , empty
    , many
    , manyTill
    , parse
    , skipMany
    , satisfy
    )

import qualified Data.Map.Strict as Map
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

{-----------------------------------------------------------------------------
    Parser functions
------------------------------------------------------------------------------}
parseFileAgdaDocumentation
    :: FilePath
        -- ^ Name of the file.
    -> String 
        -- ^ Contents of the file.
    -> Maybe AgdaDocumentation
parseFileAgdaDocumentation filename file =
    case parse haddocks filename file of
        Left _ -> Nothing
        Right x -> Just x

{-----------------------------------------------------------------------------
    Parser
------------------------------------------------------------------------------}
haddocks :: Parser AgdaDocumentation
haddocks = mkHaddocks <$> sections
  where
    mkHaddocks xs = Map.fromList $ do
        (doc, ys) <- xs
        Just ident <- [getIdentifier ys]
        [(ident, doc)]

sections :: Parser [(DocString, [Line])]
sections =
    skipMany codeLine *> many section

section :: Parser (DocString, [Line])
section = (,) <$> documentationPre <*> many codeLine

-- | Get an 'AgdaIdentifier' from a list of code lines.
getIdentifier :: [Line] -> Maybe AgdaIdentifier
getIdentifier [] = Nothing
getIdentifier (x:_) =
    case parse agdaIdentifier "" x of
        Left _ -> Nothing
        Right a -> Just a

{-----------------------------------------------------------------------------
    Lexer
------------------------------------------------------------------------------}
type Line = String

codeLine :: Parser Line
codeLine =
    start *> line
  where
    start = notFollowedBy (C.string "-- |" <|> C.string "{-|")

-- | Parse a documentation section
documentationPre :: Parser DocString
documentationPre =
    try blockDocumentationPre
        <|> linesDocumentationPre
        <|> empty

-- | Parse a sequence of line-based documentation
linesDocumentationPre :: Parser DocString
linesDocumentationPre = unlines <$> p
  where
    p = (:)
        <$> lineDocumentationPre
        <*> many (C.string "--" *> skipMany C.hspace1 *> line)

lineDocumentationPre :: Parser DocString
lineDocumentationPre =
    C.string "-- |" *> skipMany C.hspace1 *> line

blockDocumentationPre :: Parser DocString
blockDocumentationPre =
    start
        *> manyTill anySingle (C.string "-}")
        <* skipSpaceLine
  where
    start = C.string "{-|" *> skipMany C.space1
    skipSpaceLine = skipMany C.hspace1 <* C.newline

-- | Parse the rest of a line, including the newline character.
line :: Parser String
line = takeWhileP (Just "character") (/= '\n') <* C.newline

agdaIdentifier :: Parser AgdaIdentifier
agdaIdentifier = L.lexeme C.hspace1 agdaNamePart

agdaNamePart :: Parser String
agdaNamePart =
    (:)
        <$> notForbidden ("'" <> forbiddenChars)
        <*> many (notForbidden forbiddenChars)
  where
    notForbidden xs = satisfy $ not . (`elem` xs)

    forbiddenChars :: [Char]
    forbiddenChars = ".;{}()@ "
