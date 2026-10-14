{- | The parser helpers of the syntax of "Data.CFTA.Gen.Synthesis" and
"Data.CFTA.Gen.Synthesis.Liquid".
-}
module Data.CFTA.Gen.Synthesis.Internal.Syntax (
    parseWhole,
    lexeme,
    token,
) where

import Data.Text (Text)
import qualified Data.Text as Text
import Text.ParserCombinators.ReadP (ReadP, eof, readP_to_S, skipSpaces, string)

-- | Run a parser on all of the text. The error names the kind of text.
parseWhole :: String -> ReadP a -> Text -> Either String a
parseWhole kind parser text = case map fst $ readP_to_S (parser <* skipSpaces <* eof) (Text.unpack text) of
    [result] -> Right result
    [] -> Left ("cannot parse the " <> kind <> " " <> show text)
    _ -> Left ("the " <> kind <> " " <> show text <> " has more than one parse")

-- | A parser that skips the spaces before it.
lexeme :: ReadP a -> ReadP a
lexeme parser = skipSpaces *> parser

-- | A parser of a string after spaces.
token :: String -> ReadP String
token = lexeme . string
