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

import Data.List
    ( isPrefixOf
    )
import Language.Agda2hs.Agda.Parser.Types
    ( Parser
    )
import Language.Agda2hs.Agda.Types
    ( AgdaIdentifier
    , AgdaDocumentation
    , DocItem (..)
    , DocString
    , TypeSignature
    )
import Text.Megaparsec
    ( MonadParsec (notFollowedBy, takeWhileP, try)
    , (<|>)
    , anySingle
    , empty
    , many
    , manyTill
    , option
    , parse
    , skipMany
    , satisfy
    )

import qualified Data.Map.Strict as Map
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L

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
        [(ident, DocItem ident doc (getTypeSignature ys))]

sections :: Parser [(DocString, [Line])]
sections =
    skipMany codeLine *> many section

section :: Parser (DocString, [Line])
section = (,) <$> documentationPre <*> many codeLine

-- | Get an 'AgdaIdentifier' from a list of code lines.
-- Not very robust — parses an Agda name part from the first line.
getIdentifier :: [Line] -> Maybe AgdaIdentifier
getIdentifier [] = Nothing
getIdentifier (x:_) =
    case parse agdaDeclarationIdentifier "" x of
        Left _ -> Nothing
        Right a -> Just a

-- | Get a type signature from a list of code lines.
-- Not very robust — takes all lines until the first single-line comment.
getTypeSignature :: [Line] -> TypeSignature
getTypeSignature = unlines . takeWhile (not . ("--" `isPrefixOf`))

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

-- | Parse the identifier contained in a declaration
-- (term, data, record, …).
-- This parser is not very robust yet.
agdaDeclarationIdentifier :: Parser String
agdaDeclarationIdentifier =
    option () (() <$ keyword) *> agdaNamePart
  where
    keyword = L.lexeme C.space1 (foldr1 (<|>) $ map C.string keywords)
    keywords = ["data", "record", "@0"]

agdaNamePart :: Parser String
agdaNamePart =
    (:)
        <$> satisfy (notForbidden ("'" <> forbiddenChars))
        <*> takeWhileP Nothing (notForbidden forbiddenChars)
  where
    notForbidden xs = not . (`elem` xs)

    forbiddenChars :: [Char]
    forbiddenChars = ".;{}()@ "
