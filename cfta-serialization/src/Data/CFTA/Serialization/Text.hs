{-# LANGUAGE OverloadedStrings #-}

-- | Readable, exact language values with one canonical printed form.
module Data.CFTA.Serialization.Text (
    TextError (..),
    printLanguage,
    parseLanguage,
    explainTextError,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM_, unless, when)
import Data.Aeson (FromJSON, ToJSON, Value (..), encode, object, toJSON, (.=))
import qualified Data.Aeson.Key as Key
import Data.Aeson.Parser (jsonNoDup')
import qualified Data.Attoparsec.ByteString.Char8 as A
import Data.Attoparsec.Combinator (lookAhead, (<?>))
import Data.Bifunctor (first)
import qualified Data.ByteString as Bytes
import qualified Data.ByteString.Char8 as Bytes8
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.Functor (($>))
import Data.List (intersperse)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Text.Encoding.Error (lenientDecode)
import qualified Data.Text.Lazy as Lazy
import Data.Text.Lazy.Builder (Builder, fromText, toLazyText)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.Encoding as Lazy

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint (..), Guard (..))
import qualified Data.CFTA.Document as Document
import Data.CFTA.Equality.Constraint (EqConstraints (EqConstraints, EqContradiction), unPathEClass)
import qualified Data.CFTA.Formula as Formula
import qualified Data.CFTA.Language as Language
import qualified Data.CFTA.Serialization.Internal.JSON as Codec
import Data.CFTA.Symbol (Symbol, symbolRefinement, symbolText, valueName)
import Data.CFTA.Template (Template (..))

-- | A text location for syntax errors, or a shared schema and source error.
data TextError state
    = SyntaxError !Int !Int !String
    | InvalidLanguage !(Codec.DecodeError state)
    deriving (Eq, Show)

-- | Describe a syntax location or the rejected source identity.
explainTextError :: (Show state) => TextError state -> String
explainTextError failure = case failure of
    SyntaxError line column message -> "line " <> show line <> ", column " <> show column <> ": " <> message
    InvalidLanguage error' -> Codec.explainDecodeError error'

{- | Print the complete language without normalization. Parsing this form returns
that exact value when the state codec preserves equality and ordering.
Comments and input whitespace are not part of a language value.
-}
printLanguage :: (ToJSON state) => Language.Language state -> Text
printLanguage language =
    Lazy.toStrict
        $ toLazyText
        $ "language 1;\nstart "
            <> stateText (toJSON $ FTA.initialState graph)
            <> ";\n\n"
            <> foldMap rowText (Map.toAscList $ FTA.transitionTable graph)
            <> foldMap exclusionText (Map.toAscList $ Language.exclusions language)
  where
    graph = Document.sourceGraph $ Language.source language
    rowText (state, transitions) =
        "state " <> stateText (toJSON state) <> " {\n" <> foldMap transitionText transitions <> "}\n\n"
    transitionText transition =
        "  "
            <> nameText (Document.annotationName annotation)
            <> " = "
            <> symbolText' (FTA.transitionSymbol transition)
            <> childrenText (map (stateText . toJSON) $ FTA.transitionChildren transition)
            <> if Map.null facts then ";\n" else " {\n" <> foldMap factText (Map.toAscList facts) <> "  };\n"
      where
        annotation = FTA.transitionConstraint transition
        facts = Document.annotationFacts annotation
    factText (name, constraint) = "    " <> nameText name <> " = " <> constraintText constraint <> ";\n"
    exclusionText (name, exclusion) =
        "exclude " <> nameText (Language.exclusionNameText name) <> " = " <> case exclusion of
            Language.AtRoot template -> "root " <> templateText template <> ";\n"
            Language.Anywhere template -> "anywhere " <> templateText template <> ";\n"

-- | Encode a string name without changing arbitrary text or reserved names.
nameText :: Text -> Builder
nameText name
    | Just (firstChar, rest) <- Text.uncons name
    , nameStart firstChar
    , Text.all nameContinue rest
    , name /= "_" && name /= "json" =
        fromText name
    | otherwise = jsonText $ String name

-- | Retain a generic state codec when the value is not a string label.
stateText :: Value -> Builder
stateText (String name) = nameText name
stateText value = "json(" <> jsonText value <> ")"

-- | Render a complete symbol with its exact refinement.
symbolText' :: Symbol -> Builder
symbolText' symbol =
    nameText (symbolText symbol) <> case symbolRefinement symbol of
        Formula.Top -> mempty
        refinement -> " @{ " <> formulaText refinement <> " }"

-- | Render common formulas exactly, with a complete form for all other syntax.
formulaText :: Formula.Formula -> Builder
formulaText Formula.Top = "true"
formulaText Formula.Bottom = "false"
formulaText formula@(Formula.Atom relation (Formula.Var name) (Formula.Lit number))
    | name == Formula.Name (Text.pack valueName) =
        "v " <> relationText relation <> " " <> fromText (Text.pack $ show number)
    | otherwise = "raw " <> jsonText (Codec.formulaJSON formula)
formulaText formula = "raw " <> jsonText (Codec.formulaJSON formula)

-- | The six comparison tokens, in the formula's original orientation.
relationText :: Formula.Relation -> Builder
relationText relation = case relation of
    Formula.Eq -> "=="
    Formula.Ne -> "/="
    Formula.Gt -> ">"
    Formula.Ge -> ">="
    Formula.Lt -> "<"
    Formula.Le -> "<="

-- | Use concise syntax only when it preserves the complete constraint.
constraintText :: Constraint -> Builder
constraintText (Constraint (EqConstraints []) Top) = "true"
constraintText (Constraint (EqConstraints []) Bottom) = "false"
constraintText (Constraint EqContradiction Top) = "impossible"
constraintText (Constraint (EqConstraints [paths]) Top) =
    "equal(" <> separated ", " (map (jsonText . Codec.pathJSON) $ Set.toAscList $ unPathEClass paths) <> ")"
constraintText (Constraint (EqConstraints []) (Satisfies path formula)) =
    "satisfies(" <> jsonText (Codec.pathJSON path) <> ", " <> formulaText formula <> ")"
constraintText constraint = "raw " <> jsonText (Codec.constraintJSON constraint)

-- | Preserve exact, prefix, wildcard, and refined-symbol template forms.
templateText :: Template Symbol -> Builder
templateText Hole = "_"
templateText (AnyNode children) = "_(" <> separated ", " (map templateText children) <> ")"
templateText (TemplateNode symbol children) = symbolText' symbol <> childrenText (map templateText children)
templateText (AnyPrefix children) = "_(" <> separated ", " (map templateText children <> ["..."]) <> ")"
templateText (TemplatePrefix symbol children) = symbolText' symbol <> "(" <> separated ", " (map templateText children <> ["..."]) <> ")"

-- | Omit parentheses only for an exact leaf.
childrenText :: [Builder] -> Builder
childrenText [] = mempty
childrenText children = "(" <> separated ", " children <> ")"

-- | Join already rendered values without copying their text repeatedly.
separated :: Builder -> [Builder] -> Builder
separated separator = mconcat . intersperse separator

-- | The shared full representation for an arbitrary scalar or structured value.
jsonText :: Value -> Builder
jsonText = Builder.fromLazyText . Lazy.decodeUtf8 . encode

{- | Parse one complete language and apply the shared source validation.
No solver, imports, host bindings, or graph transformations run here.
-}
parseLanguage :: (Ord state, FromJSON state) => Text -> Either (TextError state) (Language.Language state)
parseLanguage input = do
    value <- finish $ A.parse (spaces *> languageParser <* A.endOfInput) bytes
    first InvalidLanguage $ Codec.languageFromJSON value
  where
    bytes = Text.encodeUtf8 input
    finish (A.Done _ value) = Right value
    finish (A.Partial continue) = finish $ continue Bytes.empty
    finish (A.Fail remaining contexts message) =
        let prefix = Text.decodeUtf8With lenientDecode $ Bytes.take (Bytes.length bytes - Bytes.length remaining) bytes
            line = 1 + Text.count "\n" prefix
            column = 1 + Text.length (Text.takeWhileEnd (/= '\n') prefix)
            detail = if null contexts then message else Text.unpack (Text.intercalate ": " $ map Text.pack contexts) <> ": " <> message
         in Left $ SyntaxError line column detail

-- | Parse the finite source rows and named exclusions of one language.
languageParser :: A.Parser Value
languageParser = do
    keyword "language"
    version <- lexeme (A.decimal :: A.Parser Integer)
    unless (version == 1) $ fail "unsupported language version"
    token ";"
    keyword "start"
    initial <- stateParser
    token ";"
    rows <- whileKeyword "state" stateParserRow
    exclusions <- untilEnd exclusionParser
    namedExclusions <- namedObject "exclusion" exclusions
    pure $
        object
            [ "format" .= ("cfta-language" :: Text)
            , "version" .= (1 :: Int)
            , "source"
                .= object ["format" .= ("cfta-document" :: Text), "version" .= (1 :: Int), "initial" .= initial, "states" .= rows]
            , "exclusions" .= namedExclusions
            ]

-- | Parse a state without discarding duplicate state identities.
stateParserRow :: A.Parser Value
stateParserRow = do
    keyword "state"
    state <- stateParser
    token "{"
    transitions <- untilClose '}' transitionParser
    token "}"
    ifNext ';' (token ";") ()
    pure $ object ["state" .= state, "transitions" .= transitions]

-- | Parse an ordered production and its separate named facts.
transitionParser :: A.Parser Value
transitionParser = do
    name <- nameParser
    token "="
    symbol <- symbolParser
    children <- ifNext '(' (parenthesized $ commaSeparated stateParser) []
    facts <- ifNext '{' (token "{" *> untilClose '}' factParser <* token "}") []
    namedFacts <- namedObject "fact" facts
    token ";"
    pure $ object ["name" .= name, "symbol" .= symbol, "children" .= children, "facts" .= namedFacts]

-- | Parse one named source constraint.
factParser :: A.Parser (Text, Value)
factParser = do
    name <- nameParser
    token "="
    constraint <- constraintParser
    token ";"
    pure (name, constraint)

-- | Parse a root or subtree exclusion without losing its name.
exclusionParser :: A.Parser (Text, Value)
exclusionParser = do
    keyword "exclude"
    name <- nameParser
    token "="
    scope <- lexeme identifier
    unless (scope == "root" || scope == "anywhere") $ fail "expected root or anywhere exclusion scope"
    template <- templateParser
    token ";"
    pure (name, Codec.tag scope [template])

-- | Preserve complete state values through the caller's JSON codec.
stateParser :: A.Parser Value
stateParser = do
    raw <- startsKeyword "json"
    if raw then keyword "json" *> parenthesized jsonParser else String <$> nameParser

-- | Parse a symbol with an optional complete refinement.
symbolParser :: A.Parser Value
symbolParser = do
    name <- nameParser
    refinement <- ifNext '@' (token "@" *> token "{" *> formulaParser <* token "}") (Codec.tag "top" [])
    pure $ object ["text" .= name, "refinement" .= refinement]

-- | Parse common formulas or an exact full formula representation.
formulaParser :: A.Parser Value
formulaParser = do
    form <- lexeme identifier
    case form of
        "raw" -> jsonParser
        "true" -> pure $ Codec.tag "top" []
        "false" -> pure $ Codec.tag "bottom" []
        "v" -> do
            relation <- relationParser
            number <- lexeme $ A.signed A.decimal
            pure $ Codec.formulaJSON $ Formula.Atom relation (Formula.Var $ Formula.Name $ Text.pack valueName) (Formula.Lit number)
        _ -> fail "expected a value comparison, true, false, or raw formula"

-- | Prefer multi-character comparisons before their prefixes.
relationParser :: A.Parser Formula.Relation
relationParser =
    token "==" $> Formula.Eq
        <|> token "/=" $> Formula.Ne
        <|> token ">=" $> Formula.Ge
        <|> token "<=" $> Formula.Le
        <|> token ">" $> Formula.Gt
        <|> token "<" $> Formula.Lt

-- | Build exact constraint syntax without conjoining or simplifying it.
constraintParser :: A.Parser Value
constraintParser = do
    form <- lexeme identifier
    case form of
        "raw" -> jsonParser
        "true" -> pure $ constraint [] $ Codec.tag "top" []
        "false" -> pure $ constraint [] $ Codec.tag "bottom" []
        "impossible" -> pure $ object ["equalities" .= Null, "guard" .= Codec.tag "top" []]
        "equal" -> do
            paths <- parenthesized $ commaSeparated jsonParser
            pure $ constraint [paths] $ Codec.tag "top" []
        "satisfies" -> parenthesized $ do
            path <- jsonParser
            token ","
            formula <- formulaParser
            pure $ constraint [] $ Codec.tag "satisfies" [path, formula]
        _ -> fail "expected true, false, impossible, equal, satisfies, or raw constraint"
  where
    constraint :: [[Value]] -> Value -> Value
    constraint equalities guard = object ["equalities" .= equalities, "guard" .= guard]

-- | Parse all five template forms while distinguishing a quoted underscore.
templateParser :: A.Parser Value
templateParser = do
    wildcard <- startsKeyword "_"
    if wildcard
        then do
            keyword "_"
            ifNext
                '('
                ( do
                    (children, prefix) <- templateArguments
                    pure $ Codec.tag (if prefix then "any-prefix" else "any-node") [toJSON children]
                )
                (Codec.tag "hole" [])
        else do
            symbol <- symbolParser
            (children, prefix) <- ifNext '(' templateArguments ([], False)
            pure $ Codec.tag (if prefix then "prefix" else "node") [symbol, toJSON children]

-- | Parse ordered children and an optional final prefix marker.
templateArguments :: A.Parser ([Value], Bool)
templateArguments = parenthesized $ go []
  where
    go reversed = do
        next <- A.peekChar
        case next of
            Just ')' -> pure (reverse reversed, False)
            Just '.' -> token "..." $> (reverse reversed, True)
            _ -> do
                child <- templateParser
                ifNext ',' (token "," *> afterComma (child : reversed)) (reverse $ child : reversed, False)
    afterComma reversed = do
        next <- A.peekChar
        when (next == Just ')') $ fail "expected a template or prefix marker after comma"
        go reversed

-- | Reject duplicate names before a map could discard their earlier values.
namedObject :: String -> [(Text, Value)] -> A.Parser Value
namedObject role entries = do
    foldM_ distinct Set.empty $ map fst entries
    pure $ object [Key.fromText name .= value | (name, value) <- entries]
  where
    distinct seen name
        | Set.member name seen = fail ("duplicate " <> role <> " name: " <> show name)
        | otherwise = pure $ Set.insert name seen

-- | Parse a quoted name or an ASCII identifier.
nameParser :: A.Parser Text
nameParser = lexeme $ do
    next <- A.peekChar
    if next == Just '"'
        then do
            value <- jsonNoDup'
            case value of
                String name -> pure name
                _ -> fail "expected a quoted name"
        else identifier

-- | Read one raw JSON value with duplicate-key rejection.
jsonParser :: A.Parser Value
jsonParser = lexeme jsonNoDup'

-- | Read an identifier without consuming presentation whitespace.
identifier :: A.Parser Text
identifier = do
    firstChar <- A.satisfy nameStart <?> "identifier or quoted name"
    rest <- A.takeWhile nameContinue
    pure $ Text.decodeUtf8 $ Bytes8.cons firstChar rest

-- | The first ASCII character of an unquoted name.
nameStart :: Char -> Bool
nameStart character = character == '_' || isAsciiLower character || isAsciiUpper character

-- | A remaining ASCII character of an unquoted name.
nameContinue :: Char -> Bool
nameContinue character = nameStart character || isDigit character || character == '-'

-- | Consume ASCII whitespace and line comments between tokens.
spaces :: A.Parser ()
spaces =
    A.skipMany $
        (A.takeWhile1 (`elem` [' ', '\t', '\r', '\n']) $> ())
            <|> (A.string "//" *> A.takeTill (== '\n') $> ())

-- | Attach presentation whitespace to one token.
lexeme :: A.Parser a -> A.Parser a
lexeme parser = parser <* spaces

-- | Require one punctuation token.
token :: Bytes.ByteString -> A.Parser ()
token spelling = lexeme (A.string spelling <?> ("expected " <> show (Bytes8.unpack spelling))) $> ()

-- | Require a complete keyword, not the prefix of an identifier.
keyword :: Bytes.ByteString -> A.Parser ()
keyword spelling = lexeme $ do
    _ <- A.string spelling <?> ("keyword " <> show (Bytes8.unpack spelling))
    next <- A.peekChar
    when (maybe False nameContinue next) $ fail "expected keyword boundary"

-- | Inspect a keyword without consuming it or hiding errors in its later body.
startsKeyword :: Bytes.ByteString -> A.Parser Bool
startsKeyword spelling = (lookAhead (keyword spelling) $> True) <|> pure False

-- | Parse an optional syntactic form only when its opening character is present.
ifNext :: Char -> A.Parser a -> a -> A.Parser a
ifNext opening parser fallback = do
    next <- A.peekChar
    if next == Just opening then parser else pure fallback

-- | Parse parentheses around a complete body.
parenthesized :: A.Parser a -> A.Parser a
parenthesized parser = token "(" *> parser <* token ")"

-- | Read a comma-separated list without accepting a trailing comma.
commaSeparated :: A.Parser a -> A.Parser [a]
commaSeparated parser = do
    next <- A.peekChar
    if next == Just ')' then pure [] else go
  where
    go = do
        value <- parser
        rest <- ifNext ',' (token "," *> go) []
        pure $ value : rest

-- | Read a block without treating an invalid item as its end.
untilClose :: Char -> A.Parser a -> A.Parser [a]
untilClose closing parser = do
    next <- A.peekChar
    if next == Just closing then pure [] else (:) <$> parser <*> untilClose closing parser

-- | Read all remaining statements without swallowing a malformed statement.
untilEnd :: A.Parser a -> A.Parser [a]
untilEnd parser = do
    next <- A.peekChar
    case next of
        Nothing -> pure []
        Just _ -> (:) <$> parser <*> untilEnd parser

-- | Read consecutive declarations with a known leading keyword.
whileKeyword :: Bytes.ByteString -> A.Parser a -> A.Parser [a]
whileKeyword spelling parser = do
    present <- startsKeyword spelling
    if present then (:) <$> parser <*> whileKeyword spelling parser else pure []
