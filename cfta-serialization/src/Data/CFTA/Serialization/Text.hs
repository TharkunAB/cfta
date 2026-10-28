{-# LANGUAGE OverloadedStrings #-}

-- | Complete readable snapshots of graphs, editable documents, languages, and checkpoints.
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

    -- * Updates
    printUpdate,
    parseUpdate,
    printUpdateWith,
    parseUpdateWith,

    -- * Checkpoints
    printCheckpoint,
    parseCheckpoint,
    printCheckpointWith,
    parseCheckpointWith,
    printSamplingCheckpoint,
    parseSamplingCheckpoint,
    printSamplingCheckpointWith,
    parseSamplingCheckpointWith,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM_, unless, when)
import Data.Attoparsec.Combinator (lookAhead, (<?>))
import qualified Data.Attoparsec.Text as A
import Data.Bifunctor (first)
import Data.Char (chr, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.Functor (($>))
import Data.List (intersperse)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Lazy
import Data.Text.Lazy.Builder (Builder, fromText, toLazyText)
import Data.Word (Word64)
import Numeric (showHex)
import Text.Read (readEither)

import qualified Data.CFTA as FTA
import Data.CFTA.Checkpoint (Checkpoint (..), SamplingCheckpoint (..))
import qualified Data.CFTA.Constraint as C
import qualified Data.CFTA.Document as D
import Data.CFTA.Equality.Constraint (
    EqConstraints (EqConstraints, EqContradiction),
    PathEClass (PathEClass),
    unPathEClass,
 )
import qualified Data.CFTA.Formula as F
import Data.CFTA.Index (ChildIndex (ChildIndex), ClassRank (ClassRank), Size (Size), Weight (Weight))
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

-- | A syntax location, a checked graph error, or a checked source-definition error.
data TextError state
    = SyntaxError !Int !Int !String
    | DuplicateState !state
    | InvalidGraph !(FTA.FTAError state Symbol)
    | InvalidDefinition !(D.DocumentError state)
    deriving (Eq, Show)

-- | Describe the input location, the rejected graph, or the rejected source identity.
explainTextError :: (Show state) => TextError state -> String
explainTextError failure = case failure of
    SyntaxError line column message -> "line " <> show line <> ", column " <> show column <> ": " <> message
    DuplicateState state -> "duplicate state row: " <> show state
    InvalidGraph (FTA.MissingInitialState state) -> "initial state " <> show state <> " has no row"
    InvalidGraph (FTA.DanglingState state) -> "child state " <> show state <> " has no row"
    InvalidGraph (FTA.InconsistentArity symbol expected actual) ->
        "symbol " <> show symbol <> " has arities " <> show expected <> " and " <> show actual
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

-- | Print an update with state labels from its 'Show' instance.
printUpdate :: (Show state) => L.Update state -> Text
printUpdate = renderUpdate (Text.pack . show)

-- | Print an update with an explicit typed state codec.
printUpdateWith :: StateCodec state -> L.Update state -> Text
printUpdateWith codec = renderUpdate (encodeState codec)

-- | Read an update with state labels from their 'Read' instance.
parseUpdate :: (Read state) => Text -> Either (TextError state) (L.Update state)
parseUpdate = readUpdate (readEither . Text.unpack)

-- | Read an update with an explicit typed state codec.
parseUpdateWith :: StateCodec state -> Text -> Either (TextError state) (L.Update state)
parseUpdateWith codec = readUpdate (decodeState codec)

{- | Print a checkpoint with state labels from their 'Show' instance. The
text holds the query and the sized rank of the next term, then the text of
'printGraph' for the graph.
-}
printCheckpoint :: (Show state) => Checkpoint state -> Text
printCheckpoint = renderCheckpoint (Text.pack . show)

-- | Print a checkpoint with an explicit typed state codec.
printCheckpointWith :: StateCodec state -> Checkpoint state -> Text
printCheckpointWith = renderCheckpoint . encodeState

-- | Read a checkpoint with its state's 'Read' instance, and validate its graph.
parseCheckpoint :: (Ord state, Read state) => Text -> Either (TextError state) (Checkpoint state)
parseCheckpoint = readCheckpoint (readEither . Text.unpack)

-- | Read a checkpoint with an explicit typed state codec.
parseCheckpointWith :: (Ord state) => StateCodec state -> Text -> Either (TextError state) (Checkpoint state)
parseCheckpointWith = readCheckpoint . decodeState

{- | Print a sampling checkpoint with state labels from their 'Show' instance.
The text holds the query, the weights, the pseudorandom generator, the seed,
and the number of draws, then the text of 'printGraph' for the graph.
-}
printSamplingCheckpoint :: (Show state) => SamplingCheckpoint state -> Text
printSamplingCheckpoint = renderSamplingCheckpoint (Text.pack . show)

-- | Print a sampling checkpoint with an explicit typed state codec.
printSamplingCheckpointWith :: StateCodec state -> SamplingCheckpoint state -> Text
printSamplingCheckpointWith = renderSamplingCheckpoint . encodeState

-- | Read a sampling checkpoint with its state's 'Read' instance, and validate its graph.
parseSamplingCheckpoint :: (Ord state, Read state) => Text -> Either (TextError state) (SamplingCheckpoint state)
parseSamplingCheckpoint = readSamplingCheckpoint (readEither . Text.unpack)

-- | Read a sampling checkpoint with an explicit typed state codec.
parseSamplingCheckpointWith ::
    (Ord state) => StateCodec state -> Text -> Either (TextError state) (SamplingCheckpoint state)
parseSamplingCheckpointWith = readSamplingCheckpoint . decodeState

-- | Render graph rows with their complete transition constraints.
renderGraph :: (state -> Text) -> FTA.PlainFTA state Symbol -> Text
renderGraph encode = built . plainGraphText encode

-- | Render the graph format.
plainGraphText :: (state -> Text) -> FTA.PlainFTA state Symbol -> Builder
plainGraphText encode = graphText "graph" encode transition
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
            <> foldMap (uncurry exclusionText) (Map.toAscList $ L.exclusions language)

-- | Render a named exclusion.
exclusionText :: L.ExclusionName -> L.Exclusion -> Builder
exclusionText name exclusion =
    "exclude " <> nameText (L.exclusionNameText name) <> " = " <> case exclusion of
        L.AtRoot template -> "root " <> templateText template <> ";\n"
        L.Anywhere template -> "anywhere " <> templateText template <> ";\n"

-- | Render the operations of an update in order, one statement each.
renderUpdate :: (state -> Text) -> L.Update state -> Text
renderUpdate encode (L.Update operations) = built $ "update 1;\n" <> foldMap operation operations
  where
    state = nameText . encode
    operation change = case change of
        L.EditSource edit -> case edit of
            D.DefineTransition at name symbol children ->
                "define "
                    <> state at
                    <> " "
                    <> nameText name
                    <> " = "
                    <> symbolText' symbol
                    <> childrenText (map state children)
                    <> ";\n"
            D.DeleteTransition at name -> "remove " <> state at <> " " <> nameText name <> ";\n"
            D.SetFact at name fact constraint ->
                "require " <> state at <> " " <> nameText name <> " " <> nameText fact <> " = " <> constraintText constraint <> ";\n"
            D.RemoveFact at name fact -> "relax " <> state at <> " " <> nameText name <> " " <> nameText fact <> ";\n"
            D.PutTransition at transition -> "put production " <> state at <> " " <> productionText "" encode transition
            D.PutRow at transitions -> "put row " <> state at <> " {\n" <> foldMap (sourceTransitionText encode) transitions <> "}\n"
            D.DeleteRow at -> "delete row " <> state at <> ";\n"
        L.Exclude name exclusion -> exclusionText name exclusion
        L.Restore name -> "restore " <> nameText (L.exclusionNameText name) <> ";\n"

-- | Render the query and the next sized rank, then the graph in the graph format.
renderCheckpoint :: (state -> Text) -> Checkpoint state -> Text
renderCheckpoint encode checkpoint =
    built $
        "checkpoint 1;\nquery "
            <> nameText (checkpointRoute checkpoint)
            <> " "
            <> integerText (checkpointVersion checkpoint)
            <> ";\nbound "
            <> integerText bound
            <> ";\nnext "
            <> integerText size
            <> " "
            <> integerText rank
            <> ";\n\n"
            <> plainGraphText encode (checkpointGraph checkpoint)
  where
    Size bound = checkpointBound checkpoint
    (Size size, ClassRank rank) = checkpointNext checkpoint

-- | Render the query, the weights, and the position of the run, then the graph in the graph format.
renderSamplingCheckpoint :: (state -> Text) -> SamplingCheckpoint state -> Text
renderSamplingCheckpoint encode checkpoint =
    built $
        "sampling 1;\nquery "
            <> nameText (samplingRoute checkpoint)
            <> " "
            <> integerText (samplingVersion checkpoint)
            <> ";\nbound "
            <> integerText bound
            <> ";\nweights "
            <> maybe "uniform" weightsText (samplingWeights checkpoint)
            <> ";\nprng "
            <> nameText (samplingPrng checkpoint)
            <> " "
            <> integerText (samplingPrngVersion checkpoint)
            <> ";\nseed "
            <> integerText (toInteger $ samplingSeed checkpoint)
            <> ";\ndraws "
            <> integerText (samplingDraws checkpoint)
            <> ";\n\n"
            <> plainGraphText encode (samplingGraph checkpoint)
  where
    Size bound = samplingBound checkpoint
    weightsText weights = listText [integerText size <> ": " <> integerText weight | (Size size, Weight weight) <- Map.toAscList weights]

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

-- | Render one named production and its individual facts in a state row.
sourceTransitionText :: (state -> Text) -> FTA.Transition state Symbol D.Annotation -> Builder
sourceTransitionText encode edge = "  " <> productionText "  " encode edge

-- | Render one named production and its individual facts, with the given indentation for its closing line.
productionText :: Builder -> (state -> Text) -> FTA.Transition state Symbol D.Annotation -> Builder
productionText indent encode edge =
    nameText (D.annotationName annotation)
        <> " = "
        <> edgeText encode edge
        <> if Map.null facts then ";\n" else " {\n" <> foldMap fact (Map.toAscList facts) <> indent <> "};\n"
  where
    annotation = FTA.transitionConstraint edge
    facts = D.annotationFacts annotation
    fact (name, constraint) = indent <> "  " <> nameText name <> " = " <> constraintText constraint <> ";\n"

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

-- | Read the query, the weights, the position, and the graph of a sampling checkpoint.
readSamplingCheckpoint ::
    (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (SamplingCheckpoint state)
readSamplingCheckpoint decode input = do
    (fields, rows) <- runParser parser input
    graph <- validGraph rows
    pure $ fields graph
  where
    parser = do
        keyword "sampling"
        format <- integerParser
        unless (format == 1) $ fail "unsupported sampling version; expected 1"
        token ";"
        keyword "query"
        route <- nameParser
        version <- integerParser
        token ";"
        keyword "bound"
        bound <- integerParser
        token ";"
        keyword "weights"
        uniform <- startsKeyword "uniform"
        weights <-
            if uniform
                then keyword "uniform" $> Nothing
                else Just . Map.fromList <$> (bracketed weight >>= distinctSizes)
        token ";"
        keyword "prng"
        algorithm <- nameParser
        algorithmVersion <- integerParser
        token ";"
        keyword "seed"
        seed <- integerParser
        when (seed < 0 || seed > toInteger (maxBound :: Word64)) $ fail "seed is outside the range of a 64-bit word"
        token ";"
        keyword "draws"
        draws <- integerParser
        token ";"
        rows <- plainGraphParser decode
        pure
            ( \graph -> SamplingCheckpoint graph route version (Size bound) weights algorithm algorithmVersion (fromInteger seed) draws
            , rows
            )
    weight = (,) <$> (Size <$> integerParser <* token ":") <*> (Weight <$> integerParser)
    distinctSizes entries = do
        foldM_ distinct Set.empty $ map fst entries
        pure entries
    distinct seen size
        | Set.member size seen = fail $ "duplicate weight of size " <> show size
        | otherwise = pure $ Set.insert size seen

-- | Read graph syntax and validate identities before constructing its row map.
readGraph ::
    (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (FTA.PlainFTA state Symbol)
readGraph decode input = runParser (plainGraphParser decode) input >>= validGraph

-- | Read the graph format: the header, the initial state, and the rows with their constraints.
plainGraphParser ::
    (Text -> Either String state) -> A.Parser (state, [(state, [FTA.Transition state Symbol C.Constraint])])
plainGraphParser decode = graphParser "graph" decode $ graphTransitionParser decode

-- | Check that each state has one row, then check the graph as 'FTA.mkFTA' does.
validGraph ::
    (Ord state) =>
    (state, [(state, [FTA.Transition state Symbol C.Constraint])]) -> Either (TextError state) (FTA.PlainFTA state Symbol)
validGraph (initial, rows) = do
    distinctStates rows
    first InvalidGraph $ FTA.mkFTA initial rows

-- | Read the query, the next sized rank, and the graph of a checkpoint.
readCheckpoint :: (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (Checkpoint state)
readCheckpoint decode input = do
    (route, version, bound, next, rows) <- runParser parser input
    graph <- validGraph rows
    pure $ Checkpoint graph route version bound next
  where
    parser = do
        keyword "checkpoint"
        format <- integerParser
        unless (format == 1) $ fail "unsupported checkpoint version; expected 1"
        token ";"
        keyword "query"
        route <- nameParser
        version <- integerParser
        token ";"
        keyword "bound"
        bound <- integerParser
        token ";"
        keyword "next"
        size <- integerParser
        rank <- integerParser
        token ";"
        rows <- plainGraphParser decode
        pure (route, version, Size bound, (Size size, ClassRank rank), rows)

-- | Reject a second row for a state.
distinctStates :: (Ord state) => [(state, rows)] -> Either (TextError state) ()
distinctStates = foldM_ distinct Set.empty . map fst
  where
    distinct seen state
        | Set.member state seen = Left $ DuplicateState state
        | otherwise = Right $ Set.insert state seen

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

-- | Read the header and the operations of an update, in order.
readUpdate :: (Text -> Either String state) -> Text -> Either (TextError state) (L.Update state)
readUpdate decode = runParser $ do
    keyword "update"
    version <- integerParser
    unless (version == 1) $ fail "unsupported update version; expected 1"
    token ";"
    L.Update <$> untilEnd operation
  where
    state = stateParser decode
    end = token ";"
    source = pure . L.EditSource
    operation = do
        word <- nameParser
        case word of
            "define" -> do
                at <- state
                name <- nameParser
                token "="
                (symbol, children) <- edgeParser decode
                end
                source $ D.DefineTransition at name symbol children
            "remove" -> (D.DeleteTransition <$> state <*> nameParser <* end) >>= source
            "require" -> do
                at <- state
                name <- nameParser
                fact <- nameParser
                token "="
                constraint <- constraintParser
                end
                source $ D.SetFact at name fact constraint
            "relax" -> (D.RemoveFact <$> state <*> nameParser <*> nameParser <* end) >>= source
            "put" -> do
                target <- nameParser
                case target of
                    "production" -> (D.PutTransition <$> state <*> sourceTransitionParser decode) >>= source
                    "row" -> do
                        at <- state
                        token "{"
                        transitions <- untilClose '}' (sourceTransitionParser decode)
                        token "}"
                        source $ D.PutRow at transitions
                    _ -> fail "expected put production or put row"
            "delete" -> keyword "row" *> ((D.DeleteRow <$> state <* end) >>= source)
            "exclude" -> uncurry L.Exclude . first L.ExclusionName <$> exclusionBody
            "restore" -> L.Restore . L.ExclusionName <$> nameParser <* end
            _ -> fail $ "expected an update operation, not " <> show word

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
    A.Parser (FTA.Transition state Symbol annotation) ->
    A.Parser (state, [(state, [FTA.Transition state Symbol annotation])])
graphParser format decode transition = do
    keyword format
    version <- integerParser
    unless (version == 1) $ fail "unsupported snapshot version; expected 1"
    token ";"
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

-- | Read a graph transition with an optional complete constraint.
graphTransitionParser :: (Text -> Either String state) -> A.Parser (FTA.Transition state Symbol C.Constraint)
graphTransitionParser decode = do
    (symbol, children) <- edgeParser decode
    present <- startsKeyword "where"
    constraint <- if present then keyword "where" *> constraintParser else pure C.noConstraint
    token ";"
    pure $ FTA.Transition symbol children constraint

-- | Read a named production and its separate facts.
sourceTransitionParser :: (Text -> Either String state) -> A.Parser (FTA.Transition state Symbol D.Annotation)
sourceTransitionParser decode = do
    name <- nameParser
    token "="
    (symbol, children) <- edgeParser decode
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
edgeParser :: (Text -> Either String state) -> A.Parser (Symbol, [state])
edgeParser decode = (,) <$> symbolParser <*> ifNext '(' (arguments $ stateParser decode) []

-- | Read a complete symbol with an optional explicit refinement.
symbolParser :: A.Parser Symbol
symbolParser = do
    name <- nameParser
    refinement <- ifNext '@' (token "@" *> token "{" *> formulaParser <* token "}") F.Top
    pure $ RefinedSymbol (Symbol name) refinement

-- | Read a named whole-term or subtree exclusion.
exclusionParser :: A.Parser (Text, L.Exclusion)
exclusionParser = keyword "exclude" *> exclusionBody

-- | Read the name, the scope, and the template of an exclusion.
exclusionBody :: A.Parser (Text, L.Exclusion)
exclusionBody = do
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
