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
    showCodec,

    -- * Notes
    Notes (..),
    CommentTarget (..),
    printGraphNotesWith,
    parseGraphNotesWith,
    printDocumentNotesWith,
    parseDocumentNotesWith,
    printLanguageNotesWith,
    parseLanguageNotesWith,

    -- * Signatures
    printSignature,
    parseSignature,
    printSignatureWith,
    parseSignatureWith,

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
import Data.Maybe (fromMaybe, isJust)
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
import Data.CFTA.Signature (SortedFunction (..), SortedSignature (..), ValueSort (..), ValueSource (..))
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

-- | State labels from the 'Show' and 'Read' instances of the state, as in 'printGraph' and 'parseGraph'.
showCodec :: (Show state, Read state) => StateCodec state
showCodec = StateCodec (Text.pack . show) (readEither . Text.unpack)

-- | The item that a doc comment documents. A production, a fact, and an exclusion are found by name.
data CommentTarget state
    = OnFile
    | OnState !state
    | -- | A production, by its state and its name.
      OnProduction !state !Text
    | -- | A fact, by its state, the name of its production, and its name.
      OnFact !state !Text !Text
    | OnExclusion !L.ExclusionName
    deriving (Eq, Ord, Show)

{- | What a file says beside its value: its doc comments, by the item that each
one documents, and the sorts of its states. Notes are not part of the value,
so they do not change the equality of the value or the text of 'printGraph'.
-}
data Notes state = Notes
    { noteComments :: Map.Map (CommentTarget state) Text
    , noteSorts :: Map.Map state Text
    -- ^ The sort of a state, as in @state Pos : Int {@.
    }
    deriving (Eq, Show)

-- | Combine the notes of two files; the left notes win on the same item.
instance (Ord state) => Semigroup (Notes state) where
    Notes leftComments leftSorts <> Notes rightComments rightSorts =
        Notes (leftComments <> rightComments) (leftSorts <> rightSorts)

instance (Ord state) => Monoid (Notes state) where
    mempty = Notes Map.empty Map.empty

-- | How a printer finds the notes of an item: its doc comment, and the sort of a state.
data NoteLookup state = NoteLookup
    { commentOf :: CommentTarget state -> Maybe Text
    , sortOf :: state -> Maybe Text
    }

-- | No notes, for the printers without notes.
noNotes :: NoteLookup state
noNotes = NoteLookup (const Nothing) (const Nothing)

-- | Find the notes of an item in 'Notes'.
lookupNotes :: (Ord state) => Notes state -> NoteLookup state
lookupNotes notes = NoteLookup (`Map.lookup` noteComments notes) (`Map.lookup` noteSorts notes)

-- | One note that a parser reads: a doc comment of an item, or the sort of a state.
data NoteEntry state
    = CommentEntry !(CommentTarget state) !Text
    | SortEntry !state !Text

-- | Collect the notes that a parser read.
notesOf :: (Ord state) => [NoteEntry state] -> Notes state
notesOf entries =
    Notes
        (Map.fromList [(target, text) | CommentEntry target text <- entries])
        (Map.fromList [(state, sort) | SortEntry state sort <- entries])

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
printGraph = renderGraph (Text.pack . show) noNotes

-- | Print a graph with an explicit typed state codec.
printGraphWith :: StateCodec state -> FTA.PlainFTA state Symbol -> Text
printGraphWith codec = renderGraph (encodeState codec) noNotes

-- | Read a graph with its state's 'Read' instance and validate its structure.
parseGraph :: (Ord state, Read state) => Text -> Either (TextError state) (FTA.PlainFTA state Symbol)
parseGraph = fmap snd . readGraph (readEither . Text.unpack)

-- | Read a graph with an explicit typed state codec.
parseGraphWith :: (Ord state) => StateCodec state -> Text -> Either (TextError state) (FTA.PlainFTA state Symbol)
parseGraphWith codec = fmap snd . readGraph (decodeState codec)

-- | Print a source document with state labels from its 'Show' instance.
printDocument :: (Show state) => D.Document state -> Text
printDocument = renderDocument (Text.pack . show) noNotes

-- | Print a source document with an explicit typed state codec.
printDocumentWith :: StateCodec state -> D.Document state -> Text
printDocumentWith codec = renderDocument (encodeState codec) noNotes

-- | Read and validate a source document with its state's 'Read' instance.
parseDocument :: (Ord state, Read state) => Text -> Either (TextError state) (D.Document state)
parseDocument = fmap snd . readDocument (readEither . Text.unpack)

-- | Read a source document with an explicit typed state codec.
parseDocumentWith :: (Ord state) => StateCodec state -> Text -> Either (TextError state) (D.Document state)
parseDocumentWith codec = fmap snd . readDocument (decodeState codec)

{- | Print an exact language value with state labels from its 'Show' instance.
A matching lawful 'Read' instance gives @parseLanguage (printLanguage x) == Right x@.
Comments and input whitespace are not part of the stored value.
-}
printLanguage :: (Show state) => L.Language state -> Text
printLanguage = renderLanguage (Text.pack . show) noNotes

-- | Print a language with an explicit typed state codec.
printLanguageWith :: StateCodec state -> L.Language state -> Text
printLanguageWith codec = renderLanguage (encodeState codec) noNotes

-- | Read an exact language value with its state's 'Read' instance.
parseLanguage :: (Ord state, Read state) => Text -> Either (TextError state) (L.Language state)
parseLanguage = fmap snd . readLanguage (readEither . Text.unpack)

-- | Read a language with an explicit typed state codec.
parseLanguageWith :: (Ord state) => StateCodec state -> Text -> Either (TextError state) (L.Language state)
parseLanguageWith codec = fmap snd . readLanguage (decodeState codec)

-- | Print a graph with the doc comments of the file and of its states. A comment on another item is not printed.
printGraphNotesWith :: (Ord state) => StateCodec state -> Notes state -> FTA.PlainFTA state Symbol -> Text
printGraphNotesWith codec notes = renderGraph (encodeState codec) (lookupNotes notes)

-- | Read a graph and the doc comments of the file and of its states.
parseGraphNotesWith ::
    (Ord state) => StateCodec state -> Text -> Either (TextError state) (Notes state, FTA.PlainFTA state Symbol)
parseGraphNotesWith = readGraph . decodeState

-- | Print a source document with the doc comments of the file, its states, its productions, and its facts.
printDocumentNotesWith :: (Ord state) => StateCodec state -> Notes state -> D.Document state -> Text
printDocumentNotesWith codec notes = renderDocument (encodeState codec) (lookupNotes notes)

-- | Read a source document and the doc comments of the file, its states, its productions, and its facts.
parseDocumentNotesWith ::
    (Ord state) => StateCodec state -> Text -> Either (TextError state) (Notes state, D.Document state)
parseDocumentNotesWith = readDocument . decodeState

-- | Print a language with the doc comments of its document and of its exclusions.
printLanguageNotesWith :: (Ord state) => StateCodec state -> Notes state -> L.Language state -> Text
printLanguageNotesWith codec notes = renderLanguage (encodeState codec) (lookupNotes notes)

-- | Read a language and the doc comments of its document and of its exclusions.
parseLanguageNotesWith ::
    (Ord state) => StateCodec state -> Text -> Either (TextError state) (Notes state, L.Language state)
parseLanguageNotesWith = readLanguage . decodeState

-- | Print a signature with sorts and symbols from their 'Show' instances.
printSignature :: (Show sort, Show symbol) => SortedSignature sort symbol -> Text
printSignature = renderSignature (Text.pack . show) (Text.pack . show)

-- | Print a signature with explicit codecs for its sorts and its symbols.
printSignatureWith :: StateCodec sort -> StateCodec symbol -> SortedSignature sort symbol -> Text
printSignatureWith sorts symbols = renderSignature (encodeState sorts) (encodeState symbols)

{- | Read a signature with the 'Read' instances of its sorts and symbols.
Reading checks the syntax only; 'Data.CFTA.Gen.ManySorted.checkSignatureWith'
of @cfta-generator@ checks the signature.
-}
parseSignature :: (Read sort, Read symbol) => Text -> Either (TextError sort) (SortedSignature sort symbol)
parseSignature = readSignature (readEither . Text.unpack) (readEither . Text.unpack)

-- | Read a signature with explicit codecs for its sorts and its symbols.
parseSignatureWith ::
    StateCodec sort -> StateCodec symbol -> Text -> Either (TextError sort) (SortedSignature sort symbol)
parseSignatureWith sorts symbols = readSignature (decodeState sorts) (decodeState symbols)

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

-- | Render graph rows with their complete transition constraints, and the doc comments that the lookup gives.
renderGraph :: (state -> Text) -> NoteLookup state -> FTA.PlainFTA state Symbol -> Text
renderGraph encode notes = built . plainGraphText encode notes

-- | Render the graph format.
plainGraphText :: (state -> Text) -> NoteLookup state -> FTA.PlainFTA state Symbol -> Builder
plainGraphText encode = graphText "graph" encode transition
  where
    transition _ edge = "  " <> edgeText encode edge <> obligation (FTA.transitionConstraint edge) <> ";\n"
    obligation constraint
        | constraint == C.noConstraint = mempty
        | otherwise = " where " <> constraintText constraint

-- | Render source rows without compiling their individual facts.
renderDocument :: (state -> Text) -> NoteLookup state -> D.Document state -> Text
renderDocument encode notes =
    built . graphText "document" encode (sourceTransitionText encode notes) notes . D.sourceGraph

-- | Render source rows and the retained exclusion expressions.
renderLanguage :: (state -> Text) -> NoteLookup state -> L.Language state -> Text
renderLanguage encode notes language =
    built $
        graphText "language" encode (sourceTransitionText encode notes) notes (D.sourceGraph $ L.source language)
            <> foldMap (uncurry $ exclusionText notes) (Map.toAscList $ L.exclusions language)

-- | Render a named exclusion after its doc comment.
exclusionText :: NoteLookup state -> L.ExclusionName -> L.Exclusion -> Builder
exclusionText notes name exclusion =
    commentText "" (commentOf notes $ OnExclusion name) <> "exclude " <> nameText (L.exclusionNameText name) <> " = " <> case exclusion of
        L.AtRoot template -> "root " <> templateText template <> ";\n"
        L.Anywhere template -> "anywhere " <> templateText template <> ";\n"

{- | Render the sorts, the roots, the value sorts, and the functions of a
signature, each list in its order, one statement for each element.
-}
renderSignature :: (sort -> Text) -> (symbol -> Text) -> SortedSignature sort symbol -> Text
renderSignature sort symbol signature =
    built $
        "signature 1;\n\n"
            <> foldMap (statement "sort") (sortedSorts signature)
            <> foldMap (statement "root") (sortedRoots signature)
            <> foldMap value (sortedValues signature)
            <> foldMap function (sortedFunctions signature)
  where
    sortText' = nameText . sort
    statement word name = word <> " " <> sortText' name <> ";\n"
    value (ValueSort name source) = "values " <> sortText' name <> " = " <> sourceText source <> ";\n"
    sourceText (Interval low high) = call "interval" [integerText low, integerText high]
    sourceText (Pool symbols) = call "pool" $ map (nameText . symbol) symbols
    function (SortedFunction name inputs result) =
        "function " <> nameText (symbol name) <> " : " <> inputsText inputs <> sortText' result <> ";\n"
    inputsText [] = mempty
    inputsText inputs = "(" <> separated (map sortText' inputs) <> ") -> "

-- | Render the operations of an update in order, one statement each.
renderUpdate :: (state -> Text) -> L.Update state -> Text
renderUpdate encode (L.Update operations) = built $ "update 1;\n" <> foldMap operation operations
  where
    state = nameText . encode
    none = noNotes
    operation change = case change of
        L.EditSource edit -> case edit of
            D.SetStart at -> "start " <> state at <> ";\n"
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
            D.PutTransition at transition -> "put production " <> state at <> " " <> productionText "" encode none at transition
            D.PutRow at transitions -> "put row " <> state at <> " {\n" <> foldMap (sourceTransitionText encode none at) transitions <> "}\n"
            D.DeleteRow at -> "delete row " <> state at <> ";\n"
        L.Exclude name exclusion -> exclusionText none name exclusion
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
            <> ";\nnext size "
            <> integerText size
            <> " rank "
            <> integerText rank
            <> ";\n\n"
            <> plainGraphText encode noNotes (checkpointGraph checkpoint)
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
            <> plainGraphText encode noNotes (samplingGraph checkpoint)
  where
    Size bound = samplingBound checkpoint
    weightsText weights = listText [integerText size <> ": " <> integerText weight | (Size size, Weight weight) <- Map.toAscList weights]

-- | Render the shared version, initial state, and finite row table, each item after its doc comment.
graphText ::
    Text ->
    (state -> Text) ->
    (state -> FTA.Transition state Symbol annotation -> Builder) ->
    NoteLookup state ->
    FTA.FTA state Symbol annotation ->
    Builder
graphText format encode transition notes graph =
    commentText "" (commentOf notes OnFile)
        <> fromText format
        <> " 1;\nstart "
        <> nameText (encode $ FTA.initialState graph)
        <> ";\n\n"
        <> foldMap row (Map.toAscList $ FTA.transitionTable graph)
  where
    row (state, edges) =
        commentText "" (commentOf notes $ OnState state)
            <> "state "
            <> nameText (encode state)
            <> maybe mempty ((" : " <>) . nameText) (sortOf notes state)
            <> " {\n"
            <> foldMap (transition state) edges
            <> "}\n\n"

-- | Render one named production and its individual facts in a state row, after its doc comment.
sourceTransitionText ::
    (state -> Text) -> NoteLookup state -> state -> FTA.Transition state Symbol D.Annotation -> Builder
sourceTransitionText encode notes state edge =
    commentText "  " (commentOf notes $ OnProduction state $ D.annotationName $ FTA.transitionConstraint edge)
        <> "  "
        <> productionText "  " encode notes state edge

-- | Render one named production and its individual facts, with the given indentation for its closing line.
productionText ::
    Builder ->
    (state -> Text) ->
    NoteLookup state ->
    state ->
    FTA.Transition state Symbol D.Annotation ->
    Builder
productionText indent encode notes state edge =
    nameText name
        <> " = "
        <> edgeText encode edge
        <> if Map.null facts then ";\n" else " {\n" <> foldMap fact (Map.toAscList facts) <> indent <> "};\n"
  where
    annotation = FTA.transitionConstraint edge
    name = D.annotationName annotation
    facts = D.annotationFacts annotation
    fact (factName, constraint) =
        commentText (indent <> "  ") (commentOf notes $ OnFact state name factName)
            <> indent
            <> "  "
            <> nameText factName
            <> " = "
            <> constraintText constraint
            <> ";\n"

-- | Render a doc comment as @///@ lines with the indentation of its item, or nothing.
commentText :: Builder -> Maybe Text -> Builder
commentText indent = maybe mempty (foldMap line . Text.splitOn "\n")
  where
    line text = indent <> "///" <> (if Text.null text then mempty else " " <> fromText text) <> "\n"

-- | Render a complete symbol and ordered child state references.
edgeText :: (state -> Text) -> FTA.Transition state Symbol annotation -> Builder
edgeText encode edge = symbolText' (FTA.transitionSymbol edge) <> childrenText (map (nameText . encode) $ FTA.transitionChildren edge)

-- | Render arbitrary labels with Unicode and escaped control characters.
nameText :: Text -> Builder
nameText name
    | not (Text.null name), Text.all nameCharacter name, name /= "_" = fromText name
    | otherwise = quotedText name

-- | Render a label in double quotes, with Unicode and escaped control characters.
quotedText :: Text -> Builder
quotedText name = "\"" <> foldMap escape (Text.unpack name) <> "\""
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
symbolText' symbol = nameText (symbolText symbol) <> refinementText symbol

-- | Render a symbol of a template. A name that starts with @_@ is quoted, because @_name@ is a named hole.
templateSymbolText :: Symbol -> Builder
templateSymbolText symbol
    | "_" `Text.isPrefixOf` symbolText symbol = quotedText (symbolText symbol) <> refinementText symbol
    | otherwise = symbolText' symbol

-- | Render the refinement of a symbol; omit only an exact top refinement.
refinementText :: Symbol -> Builder
refinementText symbol = case symbolRefinement symbol of
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
    F.Predicate (F.Name name) operands -> call "predicate" [nameText name, listText $ map termText operands]
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

-- | Render primitive, function, and named sorts.
sortText :: F.Sort -> Builder
sortText sort = case sort of
    F.IntSort -> "int"
    F.RealSort -> "real"
    F.BoolSort -> "bool"
    F.FunctionSort inputs result -> call "function" [listText $ map sortText inputs, sortText result]
    F.NamedSort (F.Name name) inputs -> call "named" [nameText name, listText $ map sortText inputs]

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
    NamedHole name -> "_" <> nameText name
    AnyNode children -> call "_" $ map templateText children
    TemplateNode symbol children -> templateSymbolText symbol <> childrenText (map templateText children)
    AnyPrefix children -> call "_" $ map templateText children <> ["..."]
    TemplatePrefix symbol children -> templateSymbolText symbol <> "(" <> separated (map templateText children <> ["..."]) <> ")"

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
        checkpointKeyword "sampling"
        format <- integerParser
        unless (format == 1) $ fail "unsupported sampling version; expected 1"
        token ";"
        checkpointKeyword "query"
        route <- nameParser
        version <- integerParser
        token ";"
        checkpointKeyword "bound"
        bound <- integerParser
        token ";"
        checkpointKeyword "weights"
        uniform <- startsKeyword "uniform"
        weights <-
            if uniform
                then keyword "uniform" $> Nothing
                else Just . Map.fromList <$> (bracketed weight >>= distinctSizes)
        token ";"
        checkpointKeyword "prng"
        algorithm <- nameParser
        algorithmVersion <- integerParser
        token ";"
        checkpointKeyword "seed"
        seed <- integerParser
        when (seed < 0 || seed > toInteger (maxBound :: Word64)) $ fail "seed is outside the range of a 64-bit word"
        token ";"
        checkpointKeyword "draws"
        draws <- integerParser
        token ";"
        (_, rows) <- plainGraphParser WithoutNotes decode
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

-- | Read graph syntax and its doc comments, and validate identities before constructing its row map.
readGraph ::
    (Ord state) =>
    (Text -> Either String state) ->
    Text ->
    Either (TextError state) (Notes state, FTA.PlainFTA state Symbol)
readGraph decode input = do
    (comments, rows) <- runParser (plainGraphParser WithNotes decode) input
    graph <- validGraph rows
    pure (notesOf comments, graph)

{- | Read the graph format: the header, the initial state, and the rows with
their constraints, and, where the rule allows them, the doc comments of the
file and of the states and the sorts of the states.
-}
plainGraphParser ::
    NoteRule ->
    (Text -> Either String state) ->
    A.Parser ([NoteEntry state], (state, [(state, [FTA.Transition state Symbol C.Constraint])]))
plainGraphParser rule decode = graphParser rule "graph" decode transition <* ruleGuard rule <* noComment
  where
    transition _ = (,) <$> graphTransitionParser decode <*> pure []

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
        checkpointKeyword "checkpoint"
        format <- integerParser
        unless (format == 1) $ fail "unsupported checkpoint version; expected 1"
        token ";"
        checkpointKeyword "query"
        route <- nameParser
        version <- integerParser
        token ";"
        checkpointKeyword "bound"
        bound <- integerParser
        token ";"
        checkpointKeyword "next"
        keyword "size"
        size <- integerParser
        keyword "rank"
        rank <- integerParser
        token ";"
        (_, rows) <- plainGraphParser WithoutNotes decode
        pure (route, version, Size bound, (Size size, ClassRank rank), rows)

-- | Reject a second row for a state.
distinctStates :: (Ord state) => [(state, rows)] -> Either (TextError state) ()
distinctStates = foldM_ distinct Set.empty . map fst
  where
    distinct seen state
        | Set.member state seen = Left $ DuplicateState state
        | otherwise = Right $ Set.insert state seen

-- | Read source syntax and its doc comments, and validate names and graph structure together.
readDocument ::
    (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (Notes state, D.Document state)
readDocument decode input = do
    (comments, (initial, rows)) <-
        runParser (graphParser WithNotes "document" decode (sourceTransitionParser decode) <* noComment) input
    document <- first InvalidDefinition $ D.mkDocument initial rows
    pure (notesOf comments, document)

-- | Read a complete language and its doc comments without compiling its constraints or exclusions.
readLanguage ::
    (Ord state) => (Text -> Either String state) -> Text -> Either (TextError state) (Notes state, L.Language state)
readLanguage decode input = do
    (comments, (initial, rows), exclusions) <- runParser parser input
    document <- first InvalidDefinition $ D.mkDocument initial rows
    pure (notesOf comments, L.Language document exclusions)
  where
    parser = do
        (comments, rows) <- graphParser WithNotes "language" decode $ sourceTransitionParser decode
        entries <- untilEnd exclusionParser
        exclusions <- namedMap "exclusion" $ map fst entries
        let exclusionComments = concat [commentOn (OnExclusion $ L.ExclusionName name) comment | ((name, _), comment) <- entries]
        pure (comments <> exclusionComments, rows, Map.mapKeys L.ExclusionName exclusions)

-- | One statement of a signature file.
data SignatureStatement sort symbol
    = SignatureSort sort
    | SignatureRoot sort
    | SignatureValues (ValueSort sort symbol)
    | SignatureFunction (SortedFunction sort symbol)

-- | Read the statements of a signature in any order, and keep the order of each kind.
readSignature ::
    (Text -> Either String sort) ->
    (Text -> Either String symbol) ->
    Text ->
    Either (TextError sort) (SortedSignature sort symbol)
readSignature decodeSort decodeSymbol = runParser $ do
    keyword "signature"
    version <- integerParser
    unless (version == 1) $ fail "unsupported signature version; expected 1"
    token ";"
    statements <- untilEnd statement
    pure $
        SortedSignature
            { sortedSorts = [name | SignatureSort name <- statements]
            , sortedFunctions = [function | SignatureFunction function <- statements]
            , sortedRoots = [name | SignatureRoot name <- statements]
            , sortedValues = [value | SignatureValues value <- statements]
            }
  where
    sort = labelParser "sort" decodeSort
    symbol = labelParser "symbol" decodeSymbol
    end = token ";"
    statement = do
        word <- nameParser
        case word of
            "sort" -> SignatureSort <$> sort <* end
            "root" -> SignatureRoot <$> sort <* end
            "values" -> do
                name <- sort
                token "="
                source <- sourceParser
                end
                pure $ SignatureValues $ ValueSort name source
            "function" -> do
                name <- symbol
                token ":"
                arguments' <- ifNext '(' (arguments sort <* token "->") []
                result <- sort
                end
                pure $ SignatureFunction $ SortedFunction name arguments' result
            _ -> fail $ "expected a signature statement, not " <> show word
    sourceParser = do
        form <- nameParser
        case form of
            "interval" -> pairArguments Interval integerParser integerParser
            "pool" -> Pool <$> arguments symbol
            _ -> fail "expected interval or pool"

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
            "start" -> (D.SetStart <$> state <* end) >>= source
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
                    "production" -> do
                        at <- state
                        (transition, _) <- sourceTransitionParser decode at
                        source $ D.PutTransition at transition
                    "row" -> do
                        at <- state
                        token "{"
                        transitions <- untilClose '}' (sourceTransitionParser decode at)
                        token "}"
                        source $ D.PutRow at $ map fst transitions
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

{- | Read the common header and finite rows, preserving duplicates for
validation, and the doc comments of the file, the states, and the transitions.
-}
graphParser ::
    NoteRule ->
    Text ->
    (Text -> Either String state) ->
    (state -> A.Parser (FTA.Transition state Symbol annotation, [NoteEntry state])) ->
    A.Parser ([NoteEntry state], (state, [(state, [FTA.Transition state Symbol annotation])]))
graphParser rule format decode transition = do
    fileComment <- ruleComment rule
    keyword format
    version <- integerParser
    unless (version == 1) $ fail "unsupported snapshot version; expected 1"
    token ";"
    ruleGuard rule
    keyword "start"
    initial <- stateParser decode
    token ";"
    rows <- whileKeyword "state" row
    pure (commentOn OnFile fileComment <> concatMap fst rows, (initial, map snd rows))
  where
    row = do
        comment <- ruleComment rule
        keyword "state"
        state <- stateParser decode
        sort <- ruleSort rule
        token "{"
        transitions <- untilClose '}' (ruleGuard rule *> transition state)
        token "}"
        ifNext ';' (token ";") ()
        pure
            ( commentOn (OnState state) comment <> maybe [] (\name -> [SortEntry state name]) sort <> concatMap snd transitions
            , (state, map fst transitions)
            )

-- | Decode one escaped state label through its typed codec.
stateParser :: (Text -> Either String state) -> A.Parser state
stateParser = labelParser "state"

-- | Decode one escaped label through a typed codec; the role names the label in an error.
labelParser :: String -> (Text -> Either String label) -> A.Parser label
labelParser role decode = do
    label <- nameParser
    either (\message -> fail $ "invalid " <> role <> " " <> show label <> ": " <> message) pure $ decode label

-- | Read a graph transition with an optional complete constraint.
graphTransitionParser :: (Text -> Either String state) -> A.Parser (FTA.Transition state Symbol C.Constraint)
graphTransitionParser decode = do
    (symbol, children) <- edgeParser decode
    present <- startsKeyword "where"
    constraint <- if present then keyword "where" *> constraintParser else pure C.noConstraint
    token ";"
    pure $ FTA.Transition symbol children constraint

-- | Read a named production of a state and its separate facts, and the doc comments of both.
sourceTransitionParser ::
    (Text -> Either String state) ->
    state ->
    A.Parser (FTA.Transition state Symbol D.Annotation, [NoteEntry state])
sourceTransitionParser decode state = do
    comment <- itemComment
    name <- nameParser
    token "="
    (symbol, children) <- edgeParser decode
    facts <- ifNext '{' (token "{" *> untilClose '}' fact <* token "}") []
    namedFacts <- namedMap "fact" [(factName, constraint) | (factName, constraint, _) <- facts]
    token ";"
    pure
        ( FTA.Transition symbol children $ D.Annotation name namedFacts
        , commentOn (OnProduction state name) comment
            <> concat [commentOn (OnFact state name factName) factComment | (factName, _, factComment) <- facts]
        )
  where
    fact = do
        comment <- itemComment
        name <- nameParser
        token "="
        constraint <- constraintParser
        token ";"
        pure (name, constraint, comment)

-- | Read a symbol and ordered child state references.
edgeParser :: (Text -> Either String state) -> A.Parser (Symbol, [state])
edgeParser decode = (,) <$> symbolParser <*> ifNext '(' (arguments $ stateParser decode) []

-- | Read a complete symbol with an optional explicit refinement.
symbolParser :: A.Parser Symbol
symbolParser = do
    name <- nameParser
    refinement <- ifNext '@' (token "@" *> token "{" *> formulaParser <* token "}") F.Top
    pure $ RefinedSymbol (Symbol name) refinement

-- | Read a named whole-term or subtree exclusion and its doc comment.
exclusionParser :: A.Parser ((Text, L.Exclusion), Maybe Text)
exclusionParser = do
    comment <- itemComment
    exclusion <- keyword "exclude" *> exclusionBody
    pure (exclusion, comment)

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
        "predicate" -> pairArguments F.Predicate (F.Name <$> nameParser) (bracketed termParser)
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

-- | Read primitive, function, and named sorts.
sortParser :: A.Parser F.Sort
sortParser = do
    form <- nameParser
    case form of
        "int" -> pure F.IntSort
        "real" -> pure F.RealSort
        "bool" -> pure F.BoolSort
        "function" -> pairArguments F.FunctionSort (bracketed sortParser) sortParser
        "named" -> pairArguments F.NamedSort (F.Name <$> nameParser) (bracketed sortParser)
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

{- | Parse all six templates. An unquoted @_@ is a hole, and @_@ directly
followed by a name is a named hole; a quoted name is a symbol.
-}
templateParser :: A.Parser (Template Symbol)
templateParser = do
    next <- A.peekChar
    if next == Just '_'
        then do
            _ <- A.char '_'
            after <- A.peekChar
            if maybe False (\c -> nameCharacter c || c == '"') after
                then NamedHole <$> nameParser
                else do
                    spaces
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

{- | Consume presentation whitespace and line comments. A line that starts with
exactly three slashes is a doc comment, which 'commentParser' reads.
-}
spaces :: A.Parser ()
spaces =
    A.skipMany $
        (A.takeWhile1 (`elem` [' ', '\t', '\r', '\n']) $> ())
            <|> lineComment
  where
    lineComment = do
        rest <- A.string "//" *> A.takeTill (== '\n')
        when ("/" `Text.isPrefixOf` rest && not ("//" `Text.isPrefixOf` rest)) $ fail "doc comment"

-- | Read the doc comment lines before an item, as one text with a newline between the lines.
commentParser :: A.Parser (Maybe Text)
commentParser = do
    commentLines <- A.many' (commentLine <* spaces)
    pure $ if null commentLines then Nothing else Just $ Text.intercalate "\n" commentLines
  where
    commentLine = A.string "///" *> (dropSpace <$> A.takeTill (== '\n'))
    dropSpace line = fromMaybe line $ Text.stripPrefix " " line

-- | Read the doc comment of an item, and reject a doc comment at the end of a block or of the input.
itemComment :: A.Parser (Maybe Text)
itemComment = do
    comment <- commentParser
    next <- A.peekChar
    when (isJust comment && maybe True (== '}') next) $ fail misplacedComment
    pure comment

-- | Reject a doc comment where no item can take it.
noComment :: A.Parser ()
noComment = do
    present <- (lookAhead (A.string "///") $> True) <|> pure False
    when present $ fail misplacedComment

-- | The error for a doc comment that does not come before an item.
misplacedComment :: String
misplacedComment = "a doc comment must come before the header, a state, a production, a fact, or an exclusion"

-- | Whether a graph can have doc comments and the sorts of its states. The graph of a checkpoint has neither.
data NoteRule = WithNotes | WithoutNotes

-- | Read the doc comment of an item, where the rule allows one.
ruleComment :: NoteRule -> A.Parser (Maybe Text)
ruleComment WithNotes = commentParser
ruleComment WithoutNotes = noCheckpointComment $> Nothing

-- | Read the sort of a state, where the rule allows one.
ruleSort :: NoteRule -> A.Parser (Maybe Text)
ruleSort WithNotes = ifNext ':' (Just <$> (token ":" *> nameParser)) Nothing
ruleSort WithoutNotes = ifNext ':' (fail "a checkpoint has no sorts") Nothing

-- | Reject a doc comment where the rule allows none.
ruleGuard :: NoteRule -> A.Parser ()
ruleGuard WithNotes = pure ()
ruleGuard WithoutNotes = noCheckpointComment

-- | Reject a doc comment in a checkpoint.
noCheckpointComment :: A.Parser ()
noCheckpointComment = do
    present <- (lookAhead (A.string "///") $> True) <|> pure False
    when present $ fail "a checkpoint has no doc comments"

-- | Read the keyword of a checkpoint statement, after a check for a doc comment.
checkpointKeyword :: Text -> A.Parser ()
checkpointKeyword word = noCheckpointComment *> keyword word

-- | A doc comment of a target, as a list of at most one note.
commentOn :: CommentTarget state -> Maybe Text -> [NoteEntry state]
commentOn target = maybe [] (\text -> [CommentEntry target text])

-- | Attach presentation whitespace to one token, and reject a doc comment before it.
lexeme :: A.Parser value -> A.Parser value
lexeme parser = noComment *> parser <* spaces

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

-- | Read consecutive declarations with a known leading keyword, each after its doc comment.
whileKeyword :: Text -> A.Parser value -> A.Parser [value]
whileKeyword spelling parser = do
    present <- (lookAhead (commentParser *> keyword spelling) $> True) <|> pure False
    if present then (:) <$> parser <*> whileKeyword spelling parser else pure []
