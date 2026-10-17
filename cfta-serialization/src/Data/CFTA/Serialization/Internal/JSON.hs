{-# LANGUAGE OverloadedStrings #-}

-- | Self-contained JSON snapshots of explicit ordinary, equality, and liquid graphs.
module Data.CFTA.Serialization.Internal.JSON (
    DecodeError (..),
    explainDecodeError,
    encodeGraph,
    decodeGraph,
    encodeDocument,
    decodeDocument,
    encodeLanguage,
    decodeLanguage,
    languageJSON,
    languageFromJSON,
    constraintJSON,
    formulaJSON,
    pathJSON,
    tag,
) where

import Control.Monad (foldM_, join, unless)
import Data.Aeson (
    FromJSON,
    Object,
    ToJSON,
    Value (..),
    encode,
    object,
    parseJSON,
    toJSON,
    withArray,
    withObject,
    withText,
    (.:),
    (.=),
 )
import Data.Aeson.Key (Key)
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Aeson.Parser (eitherDecodeWith, jsonNoDup')
import Data.Aeson.Types (JSONPath, JSONPathElement (..), Parser, formatError, iparse, iparseEither, (<?>))
import Data.Attoparsec.ByteString (endOfInput, skipWhile)
import Data.Bifunctor (first)
import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Read as Text
import qualified Data.Vector as Vector

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint (..), Guard (..), Substitution (..))
import qualified Data.CFTA.Document as Document
import Data.CFTA.Equality.Constraint (
    EqConstraints (EqConstraints, EqContradiction),
    PathEClass (PathEClass),
    unPathEClass,
 )
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Index (ChildIndex (..))
import qualified Data.CFTA.Language as Language
import Data.CFTA.Path (Path (Path), unPath)
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol), symbolRefinement, symbolText)
import Data.CFTA.Template (Template (..))

-- | A malformed document with its JSON path, or an invalid explicit graph.
data DecodeError state
    = InvalidDocument !JSONPath !String
    | InvalidGraph !(FTA.FTAError state Symbol)
    | InvalidDefinition !(Document.DocumentError state)
    deriving (Eq, Show)

-- | Render a decoding failure with its document path or graph identity.
explainDecodeError :: (Show state) => DecodeError state -> String
explainDecodeError failure = case failure of
    InvalidDocument location message -> formatError location message
    InvalidDefinition error' -> Document.explainDocumentError error'
    InvalidGraph (FTA.MissingInitialState state) -> "initial state " <> show state <> " has no row"
    InvalidGraph (FTA.DanglingState state) -> "child state " <> show state <> " has no row"
    InvalidGraph (FTA.InconsistentArity symbol expected actual) ->
        "symbol " <> show symbol <> " has arities " <> show expected <> " and " <> show actual

{- | Encode a complete graph as UTF-8 JSON, format @cfta-graph@ version 1.
The state codec must preserve state equality and ordering on a round trip.
No graph transformation or solver query occurs. This stores graph data, not
host functions, named source facts, query plans, or enumeration cursors.
-}
encodeGraph :: (ToJSON state) => FTA.PlainFTA state Symbol -> ByteString.ByteString
encodeGraph = encode . graphJSON "cfta-graph" (\constraint -> ["constraint" .= constraintJSON constraint])

-- | Encode named source facts and transition identities as @cfta-document@ version 1.
encodeDocument :: (ToJSON state) => Document.Document state -> ByteString.ByteString
encodeDocument = encode . documentJSON

-- | Encode the source value for document and language snapshots.
documentJSON :: (ToJSON state) => Document.Document state -> Value
documentJSON = graphJSON "cfta-document" annotationFields . Document.sourceGraph
  where
    annotationFields annotation =
        [ "name" .= Document.annotationName annotation
        , "facts"
            .= object
                [ Key.fromText name .= constraintJSON constraint
                | (name, constraint) <- Map.toAscList $ Document.annotationFacts annotation
                ]
        ]

-- | Store editable source and named exclusions as @cfta-language@ version 1.
encodeLanguage :: (ToJSON state) => Language.Language state -> ByteString.ByteString
encodeLanguage = encode . languageJSON

-- | The complete language value shared by the supported text formats.
languageJSON :: (ToJSON state) => Language.Language state -> Value
languageJSON language =
    object
        [ "format" .= ("cfta-language" :: Text)
        , "version" .= (1 :: Int)
        , "source" .= documentJSON (Language.source language)
        , "exclusions"
            .= object
                [ Key.fromText (Language.exclusionNameText name) .= exclusionJSON exclusion
                | (name, exclusion) <- Map.toAscList $ Language.exclusions language
                ]
        ]

-- | Read source and exclusions without lowering, pruning, or invoking a solver.
decodeLanguage ::
    (Ord state, FromJSON state) => ByteString.ByteString -> Either (DecodeError state) (Language.Language state)
decodeLanguage input = join $ first (uncurry InvalidDocument) $ readJSON parseLanguageValue input

-- | Validate a complete language value without an intermediate byte encoding.
languageFromJSON ::
    (Ord state, FromJSON state) => Value -> Either (DecodeError state) (Language.Language state)
languageFromJSON value = join $ first (uncurry InvalidDocument) $ iparseEither parseLanguageValue value

-- | Parse language fields while retaining typed structural errors.
parseLanguageValue ::
    (Ord state, FromJSON state) => Value -> Parser (Either (DecodeError state) (Language.Language state))
parseLanguageValue = fields "language" ["format", "version", "source", "exclusions"] $ \o -> do
    format <- o .: "format"
    unless (format == ("cfta-language" :: Text)) $ fail "expected format cfta-language" <?> Key "format"
    version <- o .: "version"
    unless (version == (1 :: Int)) $ fail "unsupported cfta-language version" <?> Key "version"
    (initial, rows) <- field (parseGraphData "cfta-document" parseSourceTransition) o "source"
    exclusions <-
        field
            (withObject "named exclusions" $ \values -> Map.fromList <$> traverse parseEntry (KeyMap.toList values))
            o
            "exclusions"
    pure $ do
        document <- first InvalidDefinition $ Document.mkDocument initial rows
        pure $ Language.Language document exclusions
  where
    parseEntry (name, value) = (,) (Language.ExclusionName $ Key.toText name) <$> (parseExclusion value <?> Key name)

-- | Encode the scope of an exclusion and its complete template.
exclusionJSON :: Language.Exclusion -> Value
exclusionJSON exclusion = case exclusion of
    Language.AtRoot template -> tag "root" [templateJSON template]
    Language.Anywhere template -> tag "anywhere" [templateJSON template]

-- | Read one exclusion with an explicit scope.
parseExclusion :: Value -> Parser Language.Exclusion
parseExclusion = tagged "exclusion" $ \name args -> case (name, args) of
    ("root", [template]) -> Language.AtRoot <$> at parseTemplate 1 template
    ("anywhere", [template]) -> Language.Anywhere <$> at parseTemplate 1 template
    _ -> fail "unknown exclusion tag or invalid operands"

-- | Encode all template forms, including full refined symbols.
templateJSON :: Template Symbol -> Value
templateJSON template = case template of
    Hole -> tag "hole" []
    AnyNode children -> tag "any-node" [toJSON $ map templateJSON children]
    TemplateNode symbol children -> tag "node" [symbolJSON symbol, toJSON $ map templateJSON children]
    AnyPrefix children -> tag "any-prefix" [toJSON $ map templateJSON children]
    TemplatePrefix symbol children -> tag "prefix" [symbolJSON symbol, toJSON $ map templateJSON children]

-- | Read one exact or prefix template without changing its syntax.
parseTemplate :: Value -> Parser (Template Symbol)
parseTemplate = tagged "template" $ \name args -> case (name, args) of
    ("hole", []) -> pure Hole
    ("any-node", [children]) -> AnyNode <$> at (list parseTemplate) 1 children
    ("node", [symbol, children]) -> TemplateNode <$> at parseSymbol 1 symbol <*> at (list parseTemplate) 2 children
    ("any-prefix", [children]) -> AnyPrefix <$> at (list parseTemplate) 1 children
    ("prefix", [symbol, children]) -> TemplatePrefix <$> at parseSymbol 1 symbol <*> at (list parseTemplate) 2 children
    _ -> fail "unknown template tag or invalid operands"

-- | Encode shared graph structure with the annotation fields of its format.
graphJSON :: (ToJSON state) => Text -> (annotation -> [(Key, Value)]) -> FTA.FTA state Symbol annotation -> Value
graphJSON format annotationFields graph =
    object
        [ "format" .= format
        , "version" .= (1 :: Int)
        , "initial" .= FTA.initialState graph
        , "states"
            .= [ object ["state" .= state, "transitions" .= map (transitionJSON annotationFields) transitions]
               | (state, transitions) <- Map.toAscList $ FTA.transitionTable graph
               ]
        ]

{- | Read one complete snapshot and validate references and symbol arities.
Reject duplicate JSON keys and state identities, unknown fields and tags,
unsupported versions, and trailing data. Preserve all graph rows and formula
syntax. This function does not enumerate terms or invoke a solver.
-}
decodeGraph ::
    (Ord state, FromJSON state) => ByteString.ByteString -> Either (DecodeError state) (FTA.PlainFTA state Symbol)
decodeGraph input = do
    (initial, rows) <- first (uncurry InvalidDocument) $ readJSON (parseGraphData "cfta-graph" parseTransition) input
    first InvalidGraph $ FTA.mkFTA initial rows

-- | Read and validate a source document without compiling or removing its facts.
decodeDocument ::
    (Ord state, FromJSON state) => ByteString.ByteString -> Either (DecodeError state) (Document.Document state)
decodeDocument input = do
    (initial, rows) <-
        first (uncurry InvalidDocument) $ readJSON (parseGraphData "cfta-document" parseSourceTransition) input
    first InvalidDefinition $ Document.mkDocument initial rows

-- | Require one complete JSON value and reject duplicate object keys.
readJSON :: (Value -> Parser a) -> ByteString.ByteString -> Either (JSONPath, String) a
readJSON parser = eitherDecodeWith completeJSON (iparse parser)
  where
    completeJSON = jsonNoDup' <* skipWhile (`elem` [9, 10, 13, 32]) <* endOfInput

-- | The fields and version of one snapshot, before graph validation.
parseGraphData ::
    (Ord state, FromJSON state) =>
    Text ->
    (Value -> Parser (FTA.Transition state Symbol annotation)) ->
    Value ->
    Parser (state, [(state, [FTA.Transition state Symbol annotation])])
parseGraphData expected transitionParser = fields "graph" ["format", "version", "initial", "states"] $ \o -> do
    format <- o .: "format"
    unless (format == expected) $ fail ("expected format " <> Text.unpack expected) <?> Key "format"
    version <- o .: "version"
    unless (version == (1 :: Int)) $ fail ("unsupported " <> Text.unpack expected <> " version") <?> Key "version"
    initial <- o .: "initial"
    rows <- field (list parseRow) o "states"
    foldM_ distinct Set.empty (zip [0 ..] rows)
    pure (initial, rows)
  where
    distinct seen (index, (state, _))
        | Set.member state seen = fail "duplicate state identity" <?> Key "state" <?> Index index <?> Key "states"
        | otherwise = pure $ Set.insert state seen
    parseRow = fields "state row" ["state", "transitions"] $ \o ->
        (,) <$> o .: "state" <*> field (list transitionParser) o "transitions"

-- | A transition with ordered child states and a complete annotation.
transitionJSON :: (ToJSON state) => (annotation -> [(Key, Value)]) -> FTA.Transition state Symbol annotation -> Value
transitionJSON annotationFields transition =
    object $
        [ "symbol" .= symbolJSON (FTA.transitionSymbol transition)
        , "children" .= FTA.transitionChildren transition
        ]
            <> annotationFields (FTA.transitionConstraint transition)

-- | Read a transition without interpreting its annotation.
parseTransition :: (FromJSON state) => Value -> Parser (FTA.Transition state Symbol Constraint)
parseTransition = fields "transition" ["symbol", "children", "constraint"] $ \o ->
    FTA.Transition <$> field parseSymbol o "symbol" <*> o .: "children" <*> field parseConstraint o "constraint"

-- | Read stable production names and each separate fact.
parseSourceTransition :: (FromJSON state) => Value -> Parser (FTA.Transition state Symbol Document.Annotation)
parseSourceTransition = fields "source transition" ["symbol", "children", "name", "facts"] $ \o ->
    FTA.Transition
        <$> field parseSymbol o "symbol"
        <*> o .: "children"
        <*> (Document.Annotation <$> o .: "name" <*> field parseFacts o "facts")
  where
    parseFacts = withObject "named facts" $ \facts -> Map.fromList <$> traverse parseFact (KeyMap.toList facts)
    parseFact (name, value) = (,) (Key.toText name) <$> (parseConstraint value <?> Key name)

-- | Store symbol contents, without its process-local identity.
symbolJSON :: Symbol -> Value
symbolJSON symbol = object ["text" .= symbolText symbol, "refinement" .= formulaJSON (symbolRefinement symbol)]

-- | Rebuild the local symbol identity from the stored contents.
parseSymbol :: Value -> Parser Symbol
parseSymbol = fields "symbol" ["text", "refinement"] $ \o ->
    RefinedSymbol . Symbol <$> o .: "text" <*> field parseFormula o "refinement"

-- | Preserve the compiled equality classes and the complete guard separately.
constraintJSON :: Constraint -> Value
constraintJSON (Constraint classes guard) =
    object
        [ "equalities" .= case classes of
            EqContradiction -> Null
            EqConstraints parts -> toJSON [map pathJSON $ Set.toAscList $ unPathEClass part | part <- parts]
        , "guard" .= guardJSON guard
        ]

-- | Read equality classes without merging them or simplifying the guard.
parseConstraint :: Value -> Parser Constraint
parseConstraint = fields "constraint" ["equalities", "guard"] $ \o ->
    Constraint <$> field parseClasses o "equalities" <*> field parseGuard o "guard"
  where
    parseClasses Null = pure EqContradiction
    parseClasses value = EqConstraints <$> list (fmap (PathEClass . Set.fromList) . list parsePath) value

-- | A path is an ordered array of child indexes.
pathJSON :: Path -> Value
pathJSON = toJSON . map (\(ChildIndex i) -> i) . unPath

-- | Read machine-sized child indexes, including invalid paths retained by a graph.
parsePath :: Value -> Parser Path
parsePath value = Path . map ChildIndex <$> parseJSON value

-- | Store a guard as its tag and operands.
guardJSON :: Guard -> Value
guardJSON guard = case guard of
    Top -> tag "top" []
    Bottom -> tag "bottom" []
    Same a b -> tag "same" [pathJSON a, pathJSON b]
    Entails a b -> tag "entails" [pathJSON a, pathJSON b]
    Satisfies p f -> tag "satisfies" [pathJSON p, formulaJSON f]
    Holds ps f -> tag "holds" [toJSON $ map pathJSON ps, formulaJSON f]
    Substitute substitutions nested ->
        tag
            "substitute"
            [toJSON [toJSON [pathJSON actual, pathJSON formal] | Substitution actual formal <- substitutions], guardJSON nested]
    Not nested -> tag "not" [guardJSON nested]
    And parts -> tag "and" [toJSON $ map guardJSON parts]
    Or parts -> tag "or" [toJSON $ map guardJSON parts]

-- | Read every guard form with operand paths in errors.
parseGuard :: Value -> Parser Guard
parseGuard = tagged "guard" $ \name args -> case (name, args) of
    ("top", []) -> pure Top
    ("bottom", []) -> pure Bottom
    ("same", [a, b]) -> Same <$> at parsePath 1 a <*> at parsePath 2 b
    ("entails", [a, b]) -> Entails <$> at parsePath 1 a <*> at parsePath 2 b
    ("satisfies", [p, f]) -> Satisfies <$> at parsePath 1 p <*> at parseFormula 2 f
    ("holds", [ps, f]) -> Holds <$> at (list parsePath) 1 ps <*> at parseFormula 2 f
    ("substitute", [ss, g]) -> Substitute <$> at (list parseSubstitution) 1 ss <*> at parseGuard 2 g
    ("not", [g]) -> Not <$> at parseGuard 1 g
    ("and", [gs]) -> And <$> at (list parseGuard) 1 gs
    ("or", [gs]) -> Or <$> at (list parseGuard) 1 gs
    _ -> badTag "guard" name
  where
    parseSubstitution = withArray "actual/formal paths" $ \parts -> case Vector.toList parts of
        [a, b] -> Substitution <$> at parsePath 0 a <*> at parsePath 1 b
        _ -> fail "expected two paths: actual, formal"

-- | Store a formula without normalization.
formulaJSON :: Formula.Formula -> Value
formulaJSON formula = case formula of
    Formula.Top -> tag "top" []
    Formula.Bottom -> tag "bottom" []
    Formula.And fs -> tag "and" [toJSON $ map formulaJSON fs]
    Formula.Or fs -> tag "or" [toJSON $ map formulaJSON fs]
    Formula.Not f -> tag "not" [formulaJSON f]
    Formula.Atom relation a b -> tag "atom" [relationJSON relation, termJSON a, termJSON b]
    Formula.Forall bindings f -> tag "forall" [bindingsJSON bindings, formulaJSON f]
    Formula.Exists bindings f -> tag "exists" [bindingsJSON bindings, formulaJSON f]

-- | Read formula syntax without invoking its simplifier or a solver.
parseFormula :: Value -> Parser Formula.Formula
parseFormula = tagged "formula" $ \name args -> case (name, args) of
    ("top", []) -> pure Formula.Top
    ("bottom", []) -> pure Formula.Bottom
    ("and", [fs]) -> Formula.And <$> at (list parseFormula) 1 fs
    ("or", [fs]) -> Formula.Or <$> at (list parseFormula) 1 fs
    ("not", [f]) -> Formula.Not <$> at parseFormula 1 f
    ("atom", [r, a, b]) -> Formula.Atom <$> at parseRelation 1 r <*> at parseTerm 2 a <*> at parseTerm 3 b
    ("forall", [bs, f]) -> Formula.Forall <$> at parseBindings 1 bs <*> at parseFormula 2 f
    ("exists", [bs, f]) -> Formula.Exists <$> at parseBindings 1 bs <*> at parseFormula 2 f
    _ -> badTag "formula" name

-- | Store formula terms with exact decimal integer literals.
termJSON :: Formula.Term -> Value
termJSON term = case term of
    Formula.Lit n -> tag "integer" [toJSON $ show n]
    Formula.Var (Formula.Name name) -> tag "variable" [String name]
    Formula.App (Formula.Name name) ts -> tag "application" [String name, toJSON $ map termJSON ts]
    Formula.Neg t -> tag "negate" [termJSON t]
    Formula.Add a b -> binary "add" a b
    Formula.Sub a b -> binary "subtract" a b
    Formula.Mul a b -> binary "multiply" a b
    Formula.Div a b -> binary "divide" a b
    Formula.Mod a b -> binary "modulo" a b
    Formula.Ite f a b -> tag "if" [formulaJSON f, termJSON a, termJSON b]
    Formula.Cast t s -> tag "cast" [termJSON t, sortJSON s]
  where
    binary name a b = tag name [termJSON a, termJSON b]

-- | Read formula terms with fixed tag arities.
parseTerm :: Value -> Parser Formula.Term
parseTerm = tagged "formula term" $ \name args -> case (name, args) of
    ("integer", [n]) -> Formula.Lit <$> at decimal 1 n
    ("variable", [n]) -> Formula.Var . Formula.Name <$> at parseJSON 1 n
    ("application", [n, ts]) -> Formula.App . Formula.Name <$> at parseJSON 1 n <*> at (list parseTerm) 2 ts
    ("negate", [t]) -> Formula.Neg <$> at parseTerm 1 t
    ("add", [a, b]) -> binary Formula.Add a b
    ("subtract", [a, b]) -> binary Formula.Sub a b
    ("multiply", [a, b]) -> binary Formula.Mul a b
    ("divide", [a, b]) -> binary Formula.Div a b
    ("modulo", [a, b]) -> binary Formula.Mod a b
    ("if", [f, a, b]) -> Formula.Ite <$> at parseFormula 1 f <*> at parseTerm 2 a <*> at parseTerm 3 b
    ("cast", [t, s]) -> Formula.Cast <$> at parseTerm 1 t <*> at parseSort 2 s
    _ -> badTag "formula term" name
  where
    binary constructor a b = constructor <$> at parseTerm 1 a <*> at parseTerm 2 b

-- | A canonical signed decimal integer, without a precision limit.
decimal :: Value -> Parser Integer
decimal = withText "decimal integer string" $ \text -> case Text.signed Text.decimal text of
    Right (n, rest) | Text.null rest && Text.pack (show n) == text -> pure n
    _ -> fail "expected a decimal integer string, such as 0 or -42"

-- | Store one comparison with an explicit stable tag.
relationJSON :: Formula.Relation -> Value
relationJSON relation = String $ case relation of
    Formula.Eq -> "eq"
    Formula.Ne -> "ne"
    Formula.Gt -> "gt"
    Formula.Ge -> "ge"
    Formula.Lt -> "lt"
    Formula.Le -> "le"

-- | Read one comparison tag.
parseRelation :: Value -> Parser Formula.Relation
parseRelation = withText "relation" $ \name -> case name of
    "eq" -> pure Formula.Eq
    "ne" -> pure Formula.Ne
    "gt" -> pure Formula.Gt
    "ge" -> pure Formula.Ge
    "lt" -> pure Formula.Lt
    "le" -> pure Formula.Le
    _ -> badTag "relation" name

-- | Store primitive and function sorts.
sortJSON :: Formula.Sort -> Value
sortJSON sort = case sort of
    Formula.IntSort -> tag "integer" []
    Formula.RealSort -> tag "real" []
    Formula.BoolSort -> tag "boolean" []
    Formula.FunctionSort arguments result -> tag "function" [toJSON $ map sortJSON arguments, sortJSON result]

-- | Read primitive and function sorts.
parseSort :: Value -> Parser Formula.Sort
parseSort = tagged "sort" $ \name args -> case (name, args) of
    ("integer", []) -> pure Formula.IntSort
    ("real", []) -> pure Formula.RealSort
    ("boolean", []) -> pure Formula.BoolSort
    ("function", [as, r]) -> Formula.FunctionSort <$> at (list parseSort) 1 as <*> at parseSort 2 r
    _ -> badTag "sort" name

-- | Keep quantified names and their sorts in source order.
bindingsJSON :: [(Formula.Name, Formula.Sort)] -> Value
bindingsJSON bindings = toJSON [toJSON [String name, sortJSON sort] | (Formula.Name name, sort) <- bindings]

-- | Read ordered quantified bindings.
parseBindings :: Value -> Parser [(Formula.Name, Formula.Sort)]
parseBindings = list $ withArray "name and sort" $ \parts -> case Vector.toList parts of
    [name, sort] -> (,) . Formula.Name <$> at parseJSON 0 name <*> at parseSort 1 sort
    _ -> fail "expected a name and a sort"

-- | Construct a tagged array.
tag :: Text -> [Value] -> Value
tag name args = toJSON $ String name : args

-- | Read a tagged array with an explicit operand parser.
tagged :: String -> (Text -> [Value] -> Parser a) -> Value -> Parser a
tagged label parser = withArray label $ \values -> case Vector.toList values of
    String name : args -> parser name args
    _ -> fail $ "expected a tagged " <> label <> " array"

-- | Report an unknown tag or an incorrect operand count.
badTag :: String -> Text -> Parser a
badTag label name = fail $ "unknown " <> label <> " tag or wrong operands: " <> show name

-- | Parse an array and retain the index of each element in errors.
list :: (Value -> Parser a) -> Value -> Parser [a]
list parser = withArray "array" $ \values -> traverse (uncurry $ at parser) $ zip [0 ..] $ Vector.toList values

-- | Parse one array operand at its document index.
at :: (Value -> Parser a) -> Int -> Value -> Parser a
at parser index value = parser value <?> Index index

-- | Parse one required field at its document key.
field :: (Value -> Parser a) -> Object -> Key -> Parser a
field parser o key = (o .: key >>= parser) <?> Key key

-- | Reject unknown fields before parsing an object.
fields :: String -> [Key] -> (Object -> Parser a) -> Value -> Parser a
fields label allowed parser = withObject label $ \o -> do
    foldM_ (\() key -> unless (key `elem` allowed) (fail "unknown field" <?> Key key)) () $ KeyMap.keys o
    parser o
