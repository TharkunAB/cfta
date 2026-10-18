{-# LANGUAGE OverloadedStrings #-}

-- | Complete readable snapshots of graphs, editable documents, and languages.
module Data.CFTA.Serialization.Text (
    StateCodec (..),
    TextError (..),
    explainTextError,
    printGraph,
    parseGraph,
    printGraphWith,
    parseGraphWith,
    printDocument,
    parseDocument,
    printDocumentWith,
    parseDocumentWith,
    printLanguage,
    parseLanguage,
    printLanguageWith,
    parseLanguageWith,

    -- * Graph quotes
    parseGraphQuote,
    graphQuoteNames,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM_, forM_, unless, when)
import Data.Attoparsec.Combinator (lookAhead, (<?>))
import qualified Data.Attoparsec.Text as A
import Data.Bifunctor (first)
import Data.Char (chr, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.Either (lefts)
import Data.Functor (($>))
import Data.List (intersperse)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Lazy
import Data.Text.Lazy.Builder (Builder, fromText, toLazyText)
import Numeric (showHex)
import Text.Read (readEither)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Constraint as C
import qualified Data.CFTA.Document as D
import Data.CFTA.Equality.Constraint (
    EqConstraints (EqConstraints, EqContradiction),
    PathEClass (PathEClass),
    unPathEClass,
 )
import qualified Data.CFTA.Formula as F
import Data.CFTA.Index (ChildIndex (ChildIndex))
import qualified Data.CFTA.Language as L
import Data.CFTA.Path (Path (Path), unPath)
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol), symbolRefinement, symbolText, valueName)
import Data.CFTA.Template (Template (..))

{- | A typed codec for portable state labels. Decoding an encoded state must
return that state and preserve equality and ordering. Labels are escaped by the
snapshot printer; callers do not add quotes.
-}
data StateCodec state = StateCodec
    { encodeState :: state -> Text
    , decodeState :: Text -> Either String state
    }

-- | A syntax location or a checked graph/source-definition error.
data TextError state
    = SyntaxError !Int !Int !String
    | InvalidDefinition !(D.DocumentError state)
    deriving (Eq, Show)

-- | Describe the input location or rejected source identity.
explainTextError :: (Show state) => TextError state -> String
explainTextError failure = case failure of
    SyntaxError line column message -> "line " <> show line <> ", column " <> show column <> ": " <> message
    InvalidDefinition failure' -> D.explainDocumentError failure'

-- | Print a graph with state labels from its 'Show' instance.
printGraph :: (Show state) => FTA.PlainFTA state Symbol -> Text
printGraph = renderGraph (Text.pack . show)

-- | Print a graph with an explicit typed state codec.
printGraphWith :: StateCodec state -> FTA.PlainFTA state Symbol -> Text
printGraphWith = renderGraph . encodeState

-- | Read a graph with its state's 'Read' instance and validate its structure.
parseGraph :: (Ord state, Read state) => Text -> Either (TextError state) (FTA.PlainFTA state Symbol)
parseGraph = readGraph (readEither . Text.unpack)

-- | Read a graph with an explicit typed state codec.
parseGraphWith :: (Ord state) => StateCodec state -> Text -> Either (TextError state) (FTA.PlainFTA state Symbol)
parseGraphWith = readGraph . decodeState

-- | Print a source document with state labels from its 'Show' instance.
printDocument :: (Show state) => D.Document state -> Text
printDocument = renderDocument (Text.pack . show)

-- | Print a source document with an explicit typed state codec.
printDocumentWith :: StateCodec state -> D.Document state -> Text
printDocumentWith = renderDocument . encodeState

-- | Read and validate a source document with its state's 'Read' instance.
parseDocument :: (Ord state, Read state) => Text -> Either (TextError state) (D.Document state)
parseDocument = readDocument (readEither . Text.unpack)

-- | Read a source document with an explicit typed state codec.
parseDocumentWith :: (Ord state) => StateCodec state -> Text -> Either (TextError state) (D.Document state)
parseDocumentWith = readDocument . decodeState

{- | Print an exact language value with state labels from its 'Show' instance.
A matching lawful 'Read' instance gives @parseLanguage (printLanguage x) == Right x@.
Comments and input whitespace are not part of the stored value.
-}
printLanguage :: (Show state) => L.Language state -> Text
printLanguage = renderLanguage (Text.pack . show)

-- | Print a language with an explicit typed state codec.
printLanguageWith :: StateCodec state -> L.Language state -> Text
printLanguageWith = renderLanguage . encodeState

-- | Read an exact language value with its state's 'Read' instance.
parseLanguage :: (Ord state, Read state) => Text -> Either (TextError state) (L.Language state)
parseLanguage = readLanguage (readEither . Text.unpack)

-- | Read a language with an explicit typed state codec.
parseLanguageWith :: (Ord state) => StateCodec state -> Text -> Either (TextError state) (L.Language state)
parseLanguageWith = readLanguage . decodeState

-- | Render graph rows with their complete transition constraints.
renderGraph :: (state -> Text) -> FTA.PlainFTA state Symbol -> Text
renderGraph encode = built . graphText "graph" encode transition
  where
    transition edge = "  " <> edgeText encode edge <> obligation (FTA.transitionConstraint edge) <> ";\n"
    obligation constraint
        | constraint == C.noConstraint = mempty
        | otherwise = " where " <> constraintText constraint

-- | Render source rows without compiling their individual facts.
renderDocument :: (state -> Text) -> D.Document state -> Text
renderDocument encode = built . graphText "document" encode (sourceTransitionText encode) . D.sourceGraph

-- | Render source rows and the retained exclusion expressions.
renderLanguage :: (state -> Text) -> L.Language state -> Text
renderLanguage encode language =
    built $
        graphText "language" encode (sourceTransitionText encode) (D.sourceGraph $ L.source language)
            <> foldMap exclusionText (Map.toAscList $ L.exclusions language)
  where
    exclusionText (name, exclusion) =
        "exclude " <> nameText (L.exclusionNameText name) <> " = " <> case exclusion of
            L.AtRoot template -> "root " <> templateText template <> ";\n"
            L.Anywhere template -> "anywhere " <> templateText template <> ";\n"

-- | Render the shared version, initial state, and finite row table.
graphText ::
    Text ->
    (state -> Text) ->
    (FTA.Transition state Symbol annotation -> Builder) ->
    FTA.FTA state Symbol annotation ->
    Builder
graphText format encode transition graph =
    fromText format
        <> " 1;\nstart "
        <> nameText (encode $ FTA.initialState graph)
        <> ";\n\n"
        <> foldMap row (Map.toAscList $ FTA.transitionTable graph)
  where
    row (state, edges) = "state " <> nameText (encode state) <> " {\n" <> foldMap transition edges <> "}\n\n"

-- | Render one named production and its individual facts.
sourceTransitionText :: (state -> Text) -> FTA.Transition state Symbol D.Annotation -> Builder
sourceTransitionText encode edge =
    "  "
        <> nameText (D.annotationName annotation)
        <> " = "
        <> edgeText encode edge
        <> if Map.null facts then ";\n" else " {\n" <> foldMap fact (Map.toAscList facts) <> "  };\n"
  where
    annotation = FTA.transitionConstraint edge
    facts = D.annotationFacts annotation
    fact (name, constraint) = "    " <> nameText name <> " = " <> constraintText constraint <> ";\n"

-- | Render a complete symbol and ordered child state references.
edgeText :: (state -> Text) -> FTA.Transition state Symbol annotation -> Builder
edgeText encode edge = symbolText' (FTA.transitionSymbol edge) <> childrenText (map (nameText . encode) $ FTA.transitionChildren edge)

-- | Render arbitrary labels with Unicode and escaped control characters.
nameText :: Text -> Builder
nameText name
    | not (Text.null name), Text.all nameCharacter name, name /= "_" = fromText name
    | otherwise = "\"" <> foldMap escape (Text.unpack name) <> "\""
  where
    escape '\\' = "\\\\"
    escape '"' = "\\\""
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape character
        | ord character < 32 =
            let digits = showHex (ord character) "" in fromText $ Text.pack $ "\\u" <> replicate (4 - length digits) '0' <> digits
        | otherwise = fromText $ Text.singleton character

-- | Render a complete symbol; omit only an exact top refinement.
symbolText' :: Symbol -> Builder
symbolText' symbol =
    nameText (symbolText symbol) <> case symbolRefinement symbol of
        F.Top -> mempty
        formula -> " @{ " <> formulaText formula <> " }"

-- | Render each formula constructor without normalization.
formulaText :: F.Formula -> Builder
formulaText formula = case formula of
    F.Top -> "true"
    F.Bottom -> "false"
    F.And parts -> call "and" $ map formulaText parts
    F.Or parts -> call "or" $ map formulaText parts
    F.Not inner -> call "not" [formulaText inner]
    F.Atom relation (F.Var (F.Name name)) (F.Lit number)
        | name == Text.pack valueName ->
            "v " <> relationText relation <> " " <> integerText number
    F.Atom relation left right -> call (relationName relation) [termText left, termText right]
    F.Forall bindings inner -> quantified "forall" bindings inner
    F.Exists bindings inner -> quantified "exists" bindings inner
  where
    quantified name bindings inner =
        call name [listText [nameText binding <> ": " <> sortText sort | (F.Name binding, sort) <- bindings], formulaText inner]

-- | The structural name of a comparison.
relationName :: F.Relation -> Text
relationName relation = case relation of
    F.Eq -> "eq"
    F.Ne -> "ne"
    F.Gt -> "gt"
    F.Ge -> "ge"
    F.Lt -> "lt"
    F.Le -> "le"

-- | The infix token for a distinguished-value comparison.
relationText :: F.Relation -> Builder
relationText relation = case relation of
    F.Eq -> "=="
    F.Ne -> "/="
    F.Gt -> ">"
    F.Ge -> ">="
    F.Lt -> "<"
    F.Le -> "<="

-- | Render each logic term; retain negation as distinct from a negative literal.
termText :: F.Term -> Builder
termText term = case term of
    F.Lit number -> integerText number
    F.Var (F.Name name) | name == Text.pack valueName -> "v"
    F.Var (F.Name name) -> call "var" [nameText name]
    F.App (F.Name name) operands -> call "app" [nameText name, listText $ map termText operands]
    F.Neg inner -> call "negate" [termText inner]
    F.Add left right -> binary "add" left right
    F.Sub left right -> binary "subtract" left right
    F.Mul left right -> binary "multiply" left right
    F.Div left right -> binary "divide" left right
    F.Mod left right -> binary "modulo" left right
    F.Ite condition yes no -> call "if" [formulaText condition, termText yes, termText no]
    F.Cast inner sort -> call "cast" [termText inner, sortText sort]
  where
    binary name left right = call name [termText left, termText right]

-- | Render primitive and function sorts.
sortText :: F.Sort -> Builder
sortText sort = case sort of
    F.IntSort -> "int"
    F.RealSort -> "real"
    F.BoolSort -> "bool"
    F.FunctionSort inputs result -> call "function" [listText $ map sortText inputs, sortText result]

-- | Render all guard constructors, including scoped substitutions.
guardText :: C.Guard -> Builder
guardText guard = case guard of
    C.Top -> "true"
    C.Bottom -> "false"
    C.Same left right -> call "same" [pathText left, pathText right]
    C.Entails left right -> call "entails" [pathText left, pathText right]
    C.Satisfies at formula -> call "satisfies" [pathText at, formulaText formula]
    C.Holds paths formula -> call "holds" [listText $ map pathText paths, formulaText formula]
    C.Substitute substitutions inner ->
        call
            "substitute"
            [ listText ["(" <> pathText actual <> ", " <> pathText formal <> ")" | C.Substitution actual formal <- substitutions]
            , guardText inner
            ]
    C.Not inner -> call "not" [guardText inner]
    C.And parts -> call "and" $ map guardText parts
    C.Or parts -> call "or" $ map guardText parts

-- | Retain the equality field separately from the guard.
constraintText :: C.Constraint -> Builder
constraintText (C.Constraint (EqConstraints []) guard) = guardText guard
constraintText (C.Constraint EqContradiction C.Top) = "impossible"
constraintText (C.Constraint (EqConstraints [paths]) C.Top) = call "equal" $ map pathText $ Set.toAscList $ unPathEClass paths
constraintText (C.Constraint classes guard) = call "constraint" [classesText classes, guardText guard]

-- | Render equality classes without merging or deleting them.
classesText :: EqConstraints -> Builder
classesText EqContradiction = "impossible"
classesText (EqConstraints classes) = listText [listText $ map pathText $ Set.toAscList $ unPathEClass part | part <- classes]

-- | Render all stored child indexes, including invalid paths.
pathText :: Path -> Builder
pathText = listText . map (\(ChildIndex index) -> integerText $ toInteger index) . unPath

-- | Retain each template constructor and complete refined symbol.
templateText :: Template Symbol -> Builder
templateText template = case template of
    Hole -> "_"
    AnyNode children -> call "_" $ map templateText children
    TemplateNode symbol children -> symbolText' symbol <> childrenText (map templateText children)
    AnyPrefix children -> call "_" $ map templateText children <> ["..."]
    TemplatePrefix symbol children -> symbolText' symbol <> "(" <> separated (map templateText children <> ["..."]) <> ")"

-- | Omit parentheses only for an exact leaf.
childrenText :: [Builder] -> Builder
childrenText [] = mempty
childrenText children = "(" <> separated children <> ")"

-- | Render an application of a fixed syntax constructor.
call :: Text -> [Builder] -> Builder
call name operands = fromText name <> "(" <> separated operands <> ")"

-- | Render an ordered list.
listText :: [Builder] -> Builder
listText values = "[" <> separated values <> "]"

-- | Join already rendered values without repeated copying.
separated :: [Builder] -> Builder
separated = mconcat . intersperse ", "

-- | Render an exact integer without a precision limit.
integerText :: Integer -> Builder
integerText = fromText . Text.pack . show

-- | Finish one text builder.
built :: Builder -> Text
built = Lazy.toStrict . toLazyText

-- | Read graph syntax and validate identities before constructing its row map.
readGraph ::
    (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (FTA.PlainFTA state Symbol)
readGraph decode input = do
    (initial, rows) <-
        runParser (graphParser "graph" decode $ graphTransitionParser symbolParser constraintParser C.noConstraint decode) input
    first InvalidDefinition $ do
        distinctStates rows
        first D.InvalidGraph $ FTA.mkFTA initial rows

-- | Reject a second row for a state.
distinctStates :: (Ord state) => [(state, rows)] -> Either (D.DocumentError state) ()
distinctStates = foldM_ distinct Set.empty . map fst
  where
    distinct seen state
        | Set.member state seen = Left $ D.DuplicateState state
        | otherwise = Right $ Set.insert state seen

{- | Read a graph quote: the graph format without its @graph 1;@ line. In a
quote, @\$name@ can take the place of a symbol, and @where \$name@ the place
of a constraint. The maps give the values of these names. 'FTA.mkFTA' checks
the graph, so two names for one symbol must agree on its arity.
-}
parseGraphQuote ::
    Map Text Symbol -> Map Text C.Constraint -> Text -> Either (TextError String) (FTA.PlainFTA String Symbol)
parseGraphQuote symbols constraints input = do
    (initial, rows) <- readQuote (escape "symbol" symbols) id (escape "constraint" constraints) id input
    first (InvalidDefinition . D.InvalidGraph) $ FTA.mkFTA initial rows
  where
    escape kind values name = maybe (Left $ "unknown " <> kind <> " $" <> Text.unpack name) Right $ Map.lookup name values

{- | Check the syntax and the state rows of a graph quote. Give the names of
its symbols and of its constraints that are written as @\$name@. The symbol
arities are checked when 'parseGraphQuote' reads the quote with the values.
-}
graphQuoteNames :: Text -> Either (TextError String) ([Text], [Text])
graphQuoteNames input = do
    (initial, rows) <- readQuote (Right . Left) Right (Right . Left) Right input
    let transitions = concatMap snd rows
        states = Set.fromList $ map fst rows
    first InvalidDefinition $ do
        unless (Set.member initial states) $ Left $ D.InvalidGraph $ FTA.MissingInitialState initial
        forM_ (concatMap FTA.transitionChildren transitions) $ \child ->
            unless (Set.member child states) $ Left $ D.InvalidGraph $ FTA.DanglingState child
    pure
        ( names $ map FTA.transitionSymbol transitions
        , names $ map FTA.transitionConstraint transitions
        )
  where
    names = Set.toAscList . Set.fromList . lefts

-- | Read the rows of a graph quote, with the given meaning for written and escaped symbols and constraints.
readQuote ::
    (Text -> Either String symbol) ->
    (Symbol -> symbol) ->
    (Text -> Either String constraint) ->
    (C.Constraint -> constraint) ->
    Text ->
    Either (TextError String) (String, [(String, [FTA.Transition String symbol constraint])])
readQuote symbolEscape symbol constraintEscape constraint input = do
    (initial, rows) <-
        runParser (rowsParser state $ graphTransitionParser symbols constraints (constraint C.noConstraint) state) input
    first InvalidDefinition $ distinctStates rows
    pure (initial, rows)
  where
    state = Right . Text.unpack
    symbols = escapable symbolEscape symbol symbolParser
    constraints = escapable constraintEscape constraint constraintParser

-- | Read @\$name@ and give its value, or read a written value.
escapable :: (Text -> Either String value) -> (written -> value) -> A.Parser written -> A.Parser value
escapable escape written parser = do
    next <- A.peekChar
    if next == Just '$'
        then token "$" *> (escapeName >>= either fail pure . escape)
        else written <$> parser
  where
    escapeName = lexeme (A.takeWhile1 haskellName) <?> "a Haskell name"
    haskellName character = isAsciiLower character || isAsciiUpper character || isDigit character || character `elem` ("_'." :: String)

-- | Read source syntax and validate names and graph structure together.
readDocument :: (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (D.Document state)
readDocument decode input = do
    (initial, rows) <- runParser (graphParser "document" decode $ sourceTransitionParser decode) input
    first InvalidDefinition $ D.mkDocument initial rows

-- | Read a complete language without compiling its constraints or exclusions.
readLanguage :: (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (L.Language state)
readLanguage decode input = do
    (initial, rows, exclusions) <- runParser parser input
    document <- first InvalidDefinition $ D.mkDocument initial rows
    pure $ L.Language document exclusions
  where
    parser = do
        (initial, rows) <- graphParser "language" decode $ sourceTransitionParser decode
        exclusions <- untilEnd exclusionParser >>= namedMap "exclusion"
        pure (initial, rows, Map.mapKeys L.ExclusionName exclusions)

-- | Parse one complete input and retain Unicode-aware syntax locations.
runParser :: A.Parser value -> Text -> Either (TextError state) value
runParser parser input = finish $ A.parse (spaces *> parser <* A.endOfInput) input
  where
    finish (A.Done _ value) = Right value
    finish (A.Partial continue) = finish $ continue Text.empty
    finish (A.Fail remaining contexts message) =
        let prefix = Text.take (Text.length input - Text.length remaining) input
            line = 1 + Text.count "\n" prefix
            column = 1 + Text.length (Text.takeWhileEnd (/= '\n') prefix)
            detail = if null contexts then message else Text.unpack (Text.intercalate ": " $ map Text.pack contexts) <> ": " <> message
         in Left $ SyntaxError line column detail

-- | Read the common header and finite rows, preserving duplicates for validation.
graphParser ::
    Text ->
    (Text -> Either String state) ->
    A.Parser (FTA.Transition state symbol annotation) ->
    A.Parser (state, [(state, [FTA.Transition state symbol annotation])])
graphParser format decode transition = do
    keyword format
    version <- integerParser
    unless (version == 1) $ fail "unsupported snapshot version; expected 1"
    token ";"
    rowsParser decode transition

-- | Read the initial state and the finite rows, preserving duplicates for validation.
rowsParser ::
    (Text -> Either String state) ->
    A.Parser (FTA.Transition state symbol annotation) ->
    A.Parser (state, [(state, [FTA.Transition state symbol annotation])])
rowsParser decode transition = do
    keyword "start"
    initial <- stateParser decode
    token ";"
    rows <- whileKeyword "state" row
    pure (initial, rows)
  where
    row = do
        keyword "state"
        state <- stateParser decode
        token "{"
        transitions <- untilClose '}' transition
        token "}"
        ifNext ';' (token ";") ()
        pure (state, transitions)

-- | Decode one escaped state label through its typed codec.
stateParser :: (Text -> Either String state) -> A.Parser state
stateParser decode = do
    label <- nameParser
    either (\message -> fail $ "invalid state " <> show label <> ": " <> message) pure $ decode label

-- | Read a graph transition with an optional constraint. Without @where@, the constraint is the given default.
graphTransitionParser ::
    A.Parser symbol ->
    A.Parser constraint ->
    constraint ->
    (Text -> Either String state) ->
    A.Parser (FTA.Transition state symbol constraint)
graphTransitionParser symbolRead constraintRead none decode = do
    (symbol, children) <- edgeParser symbolRead decode
    present <- startsKeyword "where"
    constraint <- if present then keyword "where" *> constraintRead else pure none
    token ";"
    pure $ FTA.Transition symbol children constraint

-- | Read a named production and its separate facts.
sourceTransitionParser :: (Text -> Either String state) -> A.Parser (FTA.Transition state Symbol D.Annotation)
sourceTransitionParser decode = do
    name <- nameParser
    token "="
    (symbol, children) <- edgeParser symbolParser decode
    facts <- ifNext '{' (token "{" *> untilClose '}' fact <* token "}") []
    namedFacts <- namedMap "fact" facts
    token ";"
    pure $ FTA.Transition symbol children $ D.Annotation name namedFacts
  where
    fact = do
        name <- nameParser
        token "="
        constraint <- constraintParser
        token ";"
        pure (name, constraint)

-- | Read a symbol and ordered child state references.
edgeParser :: A.Parser symbol -> (Text -> Either String state) -> A.Parser (symbol, [state])
edgeParser symbol decode = (,) <$> symbol <*> ifNext '(' (arguments $ stateParser decode) []

-- | Read a complete symbol with an optional explicit refinement.
symbolParser :: A.Parser Symbol
symbolParser = do
    name <- nameParser
    refinement <- ifNext '@' (token "@" *> token "{" *> formulaParser <* token "}") F.Top
    pure $ RefinedSymbol (Symbol name) refinement

-- | Read a named whole-term or subtree exclusion.
exclusionParser :: A.Parser (Text, L.Exclusion)
exclusionParser = do
    keyword "exclude"
    name <- nameParser
    token "="
    scope <- nameParser
    constructor <- case scope of
        "root" -> pure L.AtRoot
        "anywhere" -> pure L.Anywhere
        _ -> fail "expected root or anywhere exclusion scope"
    template <- templateParser
    token ";"
    pure (name, constructor template)

-- | Read every formula constructor without invoking a simplifier.
formulaParser :: A.Parser F.Formula
formulaParser = do
    form <- nameParser
    case form of
        "true" -> pure F.Top
        "false" -> pure F.Bottom
        "and" -> F.And <$> arguments formulaParser
        "or" -> F.Or <$> arguments formulaParser
        "not" -> F.Not <$> parenthesized formulaParser
        "v" -> F.Atom <$> relationParser <*> pure (F.Var $ F.Name $ Text.pack valueName) <*> (F.Lit <$> integerParser)
        "eq" -> comparison F.Eq
        "ne" -> comparison F.Ne
        "gt" -> comparison F.Gt
        "ge" -> comparison F.Ge
        "lt" -> comparison F.Lt
        "le" -> comparison F.Le
        "forall" -> quantified F.Forall
        "exists" -> quantified F.Exists
        _ -> fail "unknown formula constructor"
  where
    comparison relation = pairArguments (F.Atom relation) termParser termParser
    quantified constructor = pairArguments constructor (bracketed binding) formulaParser
    binding = (,) <$> (F.Name <$> nameParser <* token ":") <*> sortParser

-- | Read all six infix comparison tokens.
relationParser :: A.Parser F.Relation
relationParser =
    token "==" $> F.Eq
        <|> token "/=" $> F.Ne
        <|> token ">=" $> F.Ge
        <|> token "<=" $> F.Le
        <|> token ">" $> F.Gt
        <|> token "<" $> F.Lt

-- | Read exact logic terms, keeping each arithmetic constructor distinct.
termParser :: A.Parser F.Term
termParser = do
    next <- A.peekChar
    if maybe False (\c -> isDigit c || c == '-' || c == '+') next
        then F.Lit <$> integerParser
        else do
            form <- nameParser
            case form of
                "v" -> pure $ F.Var $ F.Name $ Text.pack valueName
                "var" -> F.Var . F.Name <$> parenthesized nameParser
                "app" -> pairArguments F.App (F.Name <$> nameParser) (bracketed termParser)
                "negate" -> F.Neg <$> parenthesized termParser
                "add" -> binary F.Add
                "subtract" -> binary F.Sub
                "multiply" -> binary F.Mul
                "divide" -> binary F.Div
                "modulo" -> binary F.Mod
                "if" -> parenthesized $ F.Ite <$> formulaParser <*> (token "," *> termParser) <*> (token "," *> termParser)
                "cast" -> pairArguments F.Cast termParser sortParser
                _ -> fail "unknown formula term constructor"
  where
    binary constructor = pairArguments constructor termParser termParser

-- | Read primitive and function sorts.
sortParser :: A.Parser F.Sort
sortParser = do
    form <- nameParser
    case form of
        "int" -> pure F.IntSort
        "real" -> pure F.RealSort
        "bool" -> pure F.BoolSort
        "function" -> pairArguments F.FunctionSort (bracketed sortParser) sortParser
        _ -> fail "unknown sort constructor"

-- | Read every guard constructor and ordered actual/formal substitutions.
guardParser :: A.Parser C.Guard
guardParser = nameParser >>= guardAfterName

-- | Parse the operands of one already selected guard constructor.
guardAfterName :: Text -> A.Parser C.Guard
guardAfterName form = case form of
    "true" -> pure C.Top
    "false" -> pure C.Bottom
    "same" -> pairArguments C.Same pathParser pathParser
    "entails" -> pairArguments C.Entails pathParser pathParser
    "satisfies" -> pairArguments C.Satisfies pathParser formulaParser
    "holds" -> pairArguments C.Holds (bracketed pathParser) formulaParser
    "substitute" -> pairArguments C.Substitute (bracketed substitution) guardParser
    "not" -> C.Not <$> parenthesized guardParser
    "and" -> C.And <$> arguments guardParser
    "or" -> C.Or <$> arguments guardParser
    _ -> fail "unknown guard constructor"
  where
    substitution = pairArguments C.Substitution pathParser pathParser

-- | Read exact equality syntax and the complete guard separately.
constraintParser :: A.Parser C.Constraint
constraintParser = do
    form <- nameParser
    case form of
        "equal" -> (\paths -> C.Constraint (EqConstraints [PathEClass $ Set.fromList paths]) C.Top) <$> arguments pathParser
        "impossible" -> pure $ C.Constraint EqContradiction C.Top
        "constraint" -> pairArguments C.Constraint classesParser guardParser
        _ -> C.Constraint (EqConstraints []) <$> guardAfterName form

-- | Read stored equality classes without combining or removing them.
classesParser :: A.Parser EqConstraints
classesParser = do
    impossible <- startsKeyword "impossible"
    if impossible
        then keyword "impossible" $> EqContradiction
        else EqConstraints <$> bracketed (PathEClass . Set.fromList <$> bracketed pathParser)

-- | Retain invalid stored paths, but reject indexes outside the machine range.
pathParser :: A.Parser Path
pathParser = Path <$> bracketed index
  where
    index = do
        value <- integerParser
        when (value < toInteger (minBound :: Int) || value > toInteger (maxBound :: Int)) $
            fail "child index is outside the Int range"
        pure $ ChildIndex $ fromInteger value

-- | Parse all five templates, distinguishing an unquoted hole from a symbol.
templateParser :: A.Parser (Template Symbol)
templateParser = do
    wildcard <- startsKeyword "_"
    if wildcard
        then do
            keyword "_"
            ifNext
                '('
                ( do
                    (children, prefix) <- templateArguments
                    pure $ if prefix then AnyPrefix children else AnyNode children
                )
                Hole
        else do
            symbol <- symbolParser
            (children, prefix) <- ifNext '(' templateArguments ([], False)
            pure $ if prefix then TemplatePrefix symbol children else TemplateNode symbol children

-- | Read ordered template children and an optional final prefix marker.
templateArguments :: A.Parser ([Template Symbol], Bool)
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

-- | Reject duplicate named facts or exclusions before constructing a map.
namedMap :: String -> [(Text, value)] -> A.Parser (Map.Map Text value)
namedMap role entries = do
    foldM_ distinct Set.empty $ map fst entries
    pure $ Map.fromList entries
  where
    distinct seen name
        | Set.member name seen = fail ("duplicate " <> role <> " name: " <> show name)
        | otherwise = pure $ Set.insert name seen

-- | Read an unquoted label or a quoted Unicode string.
nameParser :: A.Parser Text
nameParser = lexeme $ do
    next <- A.peekChar
    if next == Just '"' then quotedName else A.takeWhile1 nameCharacter <?> "name or quoted label"

-- | Read escaped strings without a second data-format dependency.
quotedName :: A.Parser Text
quotedName = A.char '"' *> chunks []
  where
    chunks reversed = do
        next <- A.peekChar
        case next of
            Nothing -> fail "unterminated quoted label"
            Just '"' -> A.anyChar $> Text.concat (reverse reversed)
            Just '\\' -> do
                _ <- A.anyChar
                escaped <- escape
                chunks (escaped : reversed)
            Just character
                | ord character < 32 -> fail "unescaped control character in quoted label"
                | otherwise -> do
                    plain <- A.takeWhile1 (\c -> c /= '"' && c /= '\\' && ord c >= 32)
                    chunks (plain : reversed)
    escape = do
        character <- A.anyChar
        case character of
            '"' -> pure "\""
            '\\' -> pure "\\"
            '/' -> pure "/"
            'b' -> pure "\b"
            'f' -> pure "\f"
            'n' -> pure "\n"
            'r' -> pure "\r"
            't' -> pure "\t"
            'u' -> Text.singleton <$> unicodeEscape
            _ -> fail "unknown string escape"

-- | Decode one four-digit Unicode escape, including a valid surrogate pair.
unicodeEscape :: A.Parser Char
unicodeEscape = do
    code <- hexQuad
    if code >= 0xd800 && code <= 0xdbff
        then do
            _ <- A.string "\\u"
            low <- hexQuad
            unless (low >= 0xdc00 && low <= 0xdfff) $ fail "expected a low surrogate"
            pure $ chr $ 0x10000 + (code - 0xd800) * 0x400 + low - 0xdc00
        else do
            when (code >= 0xdc00 && code <= 0xdfff) $ fail "unexpected low surrogate"
            pure $ chr code
  where
    hexQuad = do
        digits <- A.take 4
        case A.parseOnly (A.hexadecimal <* A.endOfInput) digits of
            Left _ -> fail "expected four hexadecimal digits"
            Right value -> pure value

-- | The ASCII characters permitted in an unquoted label.
nameCharacter :: Char -> Bool
nameCharacter character = isAsciiLower character || isAsciiUpper character || isDigit character || character `elem` ['_', '-', '+']

-- | Read a signed integer without silent machine overflow.
integerParser :: A.Parser Integer
integerParser = lexeme $ A.signed A.decimal

-- | Consume presentation whitespace and line comments.
spaces :: A.Parser ()
spaces =
    A.skipMany $
        (A.takeWhile1 (`elem` [' ', '\t', '\r', '\n']) $> ())
            <|> (A.string "//" *> A.takeTill (== '\n') $> ())

-- | Attach presentation whitespace to one token.
lexeme :: A.Parser value -> A.Parser value
lexeme parser = parser <* spaces

-- | Require one punctuation token.
token :: Text -> A.Parser ()
token spelling = lexeme (A.string spelling <?> ("expected " <> show spelling)) $> ()

-- | Require a complete keyword rather than a label prefix.
keyword :: Text -> A.Parser ()
keyword spelling = lexeme $ do
    _ <- A.string spelling <?> ("keyword " <> show spelling)
    next <- A.peekChar
    when (maybe False nameCharacter next) $ fail "expected keyword boundary"

-- | Inspect a keyword without consuming it or hiding errors in its body.
startsKeyword :: Text -> A.Parser Bool
startsKeyword spelling = (lookAhead (keyword spelling) $> True) <|> pure False

-- | Read an optional form only when its opening character is present.
ifNext :: Char -> A.Parser value -> value -> A.Parser value
ifNext opening parser fallback = do
    next <- A.peekChar
    if next == Just opening then parser else pure fallback

-- | Read parentheses around a complete body.
parenthesized :: A.Parser value -> A.Parser value
parenthesized parser = token "(" *> parser <* token ")"

-- | Read two fixed operands separated by a comma.
pairArguments :: (left -> right -> value) -> A.Parser left -> A.Parser right -> A.Parser value
pairArguments constructor left right = parenthesized $ constructor <$> left <*> (token "," *> right)

-- | Read a list in square brackets.
bracketed :: A.Parser value -> A.Parser [value]
bracketed parser = token "[" *> commaSeparated ']' parser <* token "]"

-- | Read a list of constructor operands.
arguments :: A.Parser value -> A.Parser [value]
arguments parser = parenthesized $ commaSeparated ')' parser

-- | Read an ordered list without accepting a trailing comma.
commaSeparated :: Char -> A.Parser value -> A.Parser [value]
commaSeparated closing parser = do
    next <- A.peekChar
    if next == Just closing then pure [] else go
  where
    go = do
        value <- parser
        rest <- ifNext ',' (token "," *> go) []
        pure $ value : rest

-- | Read a block without treating malformed items as its end.
untilClose :: Char -> A.Parser value -> A.Parser [value]
untilClose closing parser = do
    next <- A.peekChar
    if next == Just closing then pure [] else (:) <$> parser <*> untilClose closing parser

-- | Read remaining statements without swallowing syntax errors.
untilEnd :: A.Parser value -> A.Parser [value]
untilEnd parser = do
    next <- A.peekChar
    case next of
        Nothing -> pure []
        Just _ -> (:) <$> parser <*> untilEnd parser

-- | Read consecutive declarations with a known leading keyword.
whileKeyword :: Text -> A.Parser value -> A.Parser [value]
whileKeyword spelling parser = do
    present <- startsKeyword spelling
    if present then (:) <$> parser <*> whileKeyword spelling parser else pure []
