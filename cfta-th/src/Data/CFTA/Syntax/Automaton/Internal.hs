-- | Parse named graph rows and retain positions for structural errors.
module Data.CFTA.Syntax.Automaton.Internal (
    Definition (..),
    Row (..),
    Alternative (..),
    SymbolRef (..),
    parseDefinition,
    resolveDefinition,
    errorAt,
) where

import Control.Monad (foldM_)
import Data.Bifunctor (first)
import Data.List (intercalate)
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set
import Text.Parsec (
    ParseError,
    SourcePos,
    alphaNum,
    eof,
    getPosition,
    letter,
    many,
    oneOf,
    option,
    optionMaybe,
    parse,
    sepBy,
    sepBy1,
    (<|>),
 )
import Text.Parsec.Error (Message (Message), newErrorMessage)
import Text.Parsec.Language (emptyDef)
import Text.Parsec.String (Parser)
import qualified Text.Parsec.Token as Token

import qualified Data.CFTA as FTA
import Data.CFTA.Index (Arity (Arity))

-- | A value and the position at which it starts.
type Located a = (SourcePos, a)

-- | One initial state and the rows in source order.
data Definition = Definition (Located String) [Row]

-- | One state and its alternatives in source order.
data Row = Row (Located String) [Alternative]

-- | One symbol, its ordered children, and an optional constraint binding.
data Alternative = Alternative SourcePos SymbolRef [Located String] (Maybe (Located String))

-- | An ordinary label or a named symbol supplied by the caller.
data SymbolRef = Literal String | Bound String
    deriving (Eq, Ord, Show)

-- | Parse a definition and check the structure before resolving its bindings.
parseDefinition :: FilePath -> String -> Either ParseError Definition
parseDefinition source contents = do
    definition <- parse grammar source contents
    _ <- resolveDefinition label (\_ symbol -> Right symbol) (\_ _ -> Right ()) () definition
    pure definition
  where
    label (Literal text) = show text
    label (Bound name) = '$' : name

-- | Resolve bindings and validate the resulting ranked graph.
resolveDefinition ::
    (Ord symbol) =>
    (symbol -> String) ->
    (SourcePos -> SymbolRef -> Either ParseError symbol) ->
    (SourcePos -> String -> Either ParseError constraint) ->
    constraint ->
    Definition ->
    Either ParseError (FTA.FTA String symbol constraint)
resolveDefinition renderSymbol resolveSymbol resolveConstraint defaultConstraint (Definition root rows) = do
    foldM_ distinct Set.empty rows
    resolved <- traverse resolveRow rows
    first (structuralError resolved) $
        FTA.mkFTA
            (snd root)
            [ ( snd name
              , [transition{FTA.transitionChildren = map snd (FTA.transitionChildren transition)} | (_, transition) <- alternatives]
              )
            | (name, alternatives) <- resolved
            ]
  where
    distinct seen (Row (position, name) _)
        | Set.member name seen =
            Left $ errorAt position $ "state " <> show name <> " has more than one row; combine its alternatives"
        | otherwise = Right $ Set.insert name seen
    resolveRow (Row name alternatives) = do
        transitions <- traverse resolveAlternative alternatives
        pure (name, transitions)
    resolveAlternative (Alternative position symbol children annotation) = do
        resolvedSymbol <- resolveSymbol position symbol
        constraint <- maybe (Right defaultConstraint) (uncurry resolveConstraint) annotation
        pure (position, FTA.Transition resolvedSymbol children constraint)
    structuralError resolved err = case err of
        FTA.MissingInitialState name -> errorAt (fst root) $ "start state " <> show name <> " has no row"
        FTA.DanglingState name ->
            errorAt
                ( positionOf
                    [ position
                    | (_, alternatives) <- resolved
                    , (_, transition) <- alternatives
                    , (position, child) <- FTA.transitionChildren transition
                    , child == name
                    ]
                )
                $ "unknown child state " <> show name
        FTA.InconsistentArity symbol (Arity expected) (Arity actual) ->
            errorAt
                ( positionOf
                    [ position
                    | (_, alternatives) <- resolved
                    , (position, transition) <- alternatives
                    , FTA.transitionSymbol transition == symbol
                    , length (FTA.transitionChildren transition) == actual
                    ]
                )
                $ "symbol " <> renderSymbol symbol <> " has arities " <> show expected <> " and " <> show actual
    positionOf = fromMaybe (fst root) . listToMaybe

-- | A semantic error at the relevant token, independent of parser backtracking.
errorAt :: SourcePos -> String -> ParseError
errorAt position message = newErrorMessage (Message message) position

-- | The complete graph syntax, with one required initial-state declaration.
grammar :: Parser Definition
grammar = do
    Token.whiteSpace lexer
    Token.reserved lexer "start"
    root <- located (Token.identifier lexer)
    _ <- Token.semi lexer
    rows <- many row
    eof
    pure $ Definition root rows

-- | A state row. An empty list of alternatives retains an empty state.
row :: Parser Row
row = do
    name <- located (Token.identifier lexer)
    _ <- Token.symbol lexer "="
    alternatives <- alternative `sepBy` Token.symbol lexer "|"
    _ <- Token.semi lexer
    pure $ Row name alternatives

-- | One transition, including optional children and a constraint binding.
alternative :: Parser Alternative
alternative = do
    position <- getPosition
    symbol <- (Literal <$> Token.stringLiteral lexer) <|> (Bound <$> (Token.symbol lexer "$" *> qualifiedName))
    children <- option [] $ Token.parens lexer $ Token.commaSep lexer $ located $ Token.identifier lexer
    annotation <- optionMaybe $ Token.reserved lexer "where" *> located qualifiedName
    pure $ Alternative position symbol children annotation

-- | An unqualified or module-qualified Haskell binding name.
qualifiedName :: Parser String
qualifiedName = intercalate "." <$> Token.identifier lexer `sepBy1` Token.symbol lexer "."

-- | Retain the start position of one parsed value.
located :: Parser a -> Parser (Located a)
located parser = do
    position <- getPosition
    value <- parser
    pure (position, value)

-- | Identifiers, Haskell string escapes, and line comments.
lexer :: Token.TokenParser ()
lexer =
    Token.makeTokenParser
        emptyDef
            { Token.commentLine = "--"
            , Token.identStart = letter <|> oneOf "_"
            , Token.identLetter = alphaNum <|> oneOf "_'"
            , Token.reservedNames = ["start", "where"]
            }
