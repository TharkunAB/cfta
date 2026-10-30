{-# LANGUAGE OverloadedStrings #-}

{- | A model of the programs of a library, which orders the fits of a hole.

A fit model holds the counts of a corpus of programs: how often each symbol
occurs, and how often it occurs as the argument at each position of each
parent symbol. A symbol is the name of a leaf with its number of arguments,
as @map/2@. A name that is not a candidate of the model is @var@: an
argument of the query or another local name. 'tokenScore' gives the
logarithm of the probability of a token given its parent's token and its
position; the score of a fit is the sum over its tokens. Mode (b) with
'Data.CFTA.GHC.Fits.optionScore' checks the fits in the order of descending
score.

The probability of a symbol @s@ as the argument at position @i@ of a parent
@p@ mixes two parts. The first is the relative frequency @c(p, i, s) / c(p,
i)@, where @c(p, i)@ is the count of all symbols in that context. The second
is the probability of the symbol alone, @(c(s) + 1) / (N + A)@, where @N@ is
the count of all symbols and @A@ is the size of the alphabet. The mix is
@λ = c(p, i) / (c(p, i) + t(p, i))@ for the first part, where @t(p, i)@ is the
number of distinct symbols seen in the context, and @1 - λ@ for the second
(the interpolation of Witten and Bell, /The Zero-Frequency Problem/, IEEE
Transactions on Information Theory 1991). A context without counts has the
probability of the symbol alone. The root of a fit has the parent @top@ and
the position 0: in the corpus, @top@ is the parent of the root of each
right-hand side, and @expr@ is the parent of the root of each other
application. The logarithm of each such probability is a log-weight of a
symbol in a context, as in "Data.CFTA.Sized.Prefix.Model".

The alphabet is every candidate with each number of arguments up to its
arity, @var@ and @other@ with 0 to 4 arguments, and every symbol of the
counts. Counts are integers, so two models of the same candidates merge by
adding their counts ('merge'): a project can add a model of its own code to
a model of Hackage.

= The text form @fit-model 1;@

A file of a fit model has the extension @.cfta@, as @base.cfta@.

Each record is one line, which ends with a semicolon; the words are separated
by spaces. The first line is @fit-model 1;@. Then, in any order:

* @modules NAME...;@: the modules of the candidates, as a record of where
  they come from;
* @candidate NAME ARITY;@: a candidate and its number of arguments;
* @unigram SYMBOL COUNT;@: the count of a symbol;
* @context PARENT POSITION SYMBOL COUNT;@: the count of a symbol at a position
  of a parent symbol (or of @top@ or @expr@).

'printFitModel' writes the records in a fixed order, and 'parseFitModel'
reads them back.
-}
module Data.CFTA.GHC.Model (
    FitModel (..),
    fromTerms,
    merge,
    scale,
    tokenScore,
    tokenScoreAt,
    symbolOf,
    printFitModel,
    parseFitModel,
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Read (readMaybe)

import Data.CFTA.Term (Term (..))

-- | The counts of a corpus of programs.
data FitModel = FitModel
    { modelModules :: [Text]
    -- ^ The modules of the candidates.
    , modelCandidates :: Map Text Int
    -- ^ Each candidate with its number of arguments.
    , modelUnigrams :: Map Text Integer
    -- ^ The count of each symbol.
    , modelContexts :: Map (Text, Int, Text) Integer
    -- ^ The count of each symbol at a position of a parent symbol.
    }
    deriving (Eq, Show)

{- | The model of a corpus of terms, each with the parent of its root (@top@
for the root of a right-hand side, @expr@ for another application). Each
symbol of a term is a name with its number of arguments, as @map/2@.
-}
fromTerms :: [Text] -> Map Text Int -> [(Text, Term Text)] -> FitModel
fromTerms modules candidates terms =
    FitModel
        { modelModules = modules
        , modelCandidates = candidates
        , modelUnigrams = Map.fromListWith (+) [(symbol, 1) | (_, term) <- terms, symbol <- foldr (:) [] term]
        , modelContexts = Map.fromListWith (+) [(key, 1) | (root, term) <- terms, key <- withParents root 0 term]
        }
  where
    withParents parent position (Node symbol children) =
        (parent, position, symbol) : concat [withParents symbol index child | (index, child) <- zip [0 ..] children]

{- | Two models together: the union of their modules and candidates, and the
sums of their counts. A candidate with two arities keeps the larger one.
-}
merge :: FitModel -> FitModel -> FitModel
merge left right =
    FitModel
        { modelModules = Set.toList (Set.fromList (modelModules left <> modelModules right))
        , modelCandidates = Map.unionWith max (modelCandidates left) (modelCandidates right)
        , modelUnigrams = Map.unionWith (+) (modelUnigrams left) (modelUnigrams right)
        , modelContexts = Map.unionWith (+) (modelContexts left) (modelContexts right)
        }

-- | A model whose counts are each multiplied by a number, for a part that counts more in a 'merge'.
scale :: Integer -> FitModel -> FitModel
scale factor model =
    model
        { modelUnigrams = Map.map (* factor) (modelUnigrams model)
        , modelContexts = Map.map (* factor) (modelContexts model)
        }

{- | The symbol of a token: its name, without the number after a space that
names a specialization, and its number of arguments. A name that is not a
candidate is @var@.
-}
symbolOf :: FitModel -> (Text, Int) -> Text
symbolOf model (name, arguments) =
    let base = Text.takeWhile (/= ' ') name
     in (if Map.member base (modelCandidates model) then base else "var") <> "/" <> Text.pack (show arguments)

{- | The score of a token given its parent's token (none for the root of a
fit, whose parent is @top@) and its position: the logarithm of its
probability, as the module header gives it. Apply the function to the model
once, and the result to each token: the totals of the contexts are computed
once.
-}
tokenScore :: FitModel -> Maybe (Text, Int) -> Int -> (Text, Int) -> Double
tokenScore model = tokenScoreAt model ("top", 0)

{- | 'tokenScore' with the context of the root of the fit: a parent symbol (as
@foldr/3@, or @top@) and a position, as for a hole that is an argument of an
application ("Data.CFTA.GHC.Corpus.holeContext").
-}
tokenScoreAt :: FitModel -> (Text, Int) -> Maybe (Text, Int) -> Int -> (Text, Int) -> Double
tokenScoreAt model (rootParent, rootPosition) = \parent position token -> case parent of
    Nothing -> log (probability rootParent rootPosition (symbolOf model token))
    Just above -> log (probability (symbolOf model above) position (symbolOf model token))
  where
    alphabet =
        fromIntegral . Set.size . Set.fromList $
            [name <> "/" <> Text.pack (show count) | (name, arity) <- Map.toList (modelCandidates model), count <- [0 .. arity]]
                <> [name <> "/" <> Text.pack (show count) | name <- ["var", "other"], count <- [0 .. 4 :: Int]]
                <> Map.keys (modelUnigrams model) ::
            Double
    total = fromIntegral (sum (Map.elems (modelUnigrams model))) :: Double
    contexts =
        Map.fromListWith
            (\(count, kinds) (count', kinds') -> (count + count', kinds + kinds'))
            [((parent, position), (fromIntegral count, 1)) | ((parent, position, _), count) <- Map.toList (modelContexts model)] ::
            Map (Text, Int) (Double, Double)
    alone symbol = (fromIntegral (Map.findWithDefault 0 symbol (modelUnigrams model)) + 1) / (total + alphabet)
    probability parent position symbol = case Map.lookup (parent, position) contexts of
        Nothing -> alone symbol
        Just (count, kinds) ->
            let mix = count / (count + kinds)
                seen = fromIntegral (Map.findWithDefault 0 (parent, position, symbol) (modelContexts model))
             in mix * seen / count + (1 - mix) * alone symbol

-- | The text form @fit-model 1;@ of a model.
printFitModel :: FitModel -> Text
printFitModel model =
    Text.unlines $
        ["fit-model 1;", record ("modules" : modelModules model)]
            <> [record ["candidate", name, number arity] | (name, arity) <- Map.toList (modelCandidates model)]
            <> [record ["unigram", symbol, number count] | (symbol, count) <- Map.toList (modelUnigrams model)]
            <> [ record ["context", parent, number position, symbol, number count]
               | ((parent, position, symbol), count) <- Map.toList (modelContexts model)
               ]
  where
    record words' = Text.unwords words' <> ";"
    number :: (Show a) => a -> Text
    number = Text.pack . show

{- | Read the text form @fit-model 1;@. The error gives the number of the
first line that is not a record of the form, and the line.
-}
parseFitModel :: Text -> Either String FitModel
parseFitModel text = case zip [1 :: Int ..] (Text.lines text) of
    (_, "fit-model 1;") : rest ->
        foldl
            step
            (Right (FitModel [] Map.empty Map.empty Map.empty))
            [line | line@(_, content) <- rest, not (Text.null (Text.strip content))]
    (_, first) : _ -> Left ("fit-model: the first line is not \"fit-model 1;\": " <> Text.unpack first)
    [] -> Left "fit-model: the text is empty"
  where
    step (Left message) _ = Left message
    step (Right model) (number, line) = case Text.stripSuffix ";" (Text.strip line) of
        Nothing -> bad number line
        Just content -> case Text.words content of
            "modules" : names -> Right model{modelModules = modelModules model <> names}
            ["candidate", name, arity] | Just found <- readText arity -> Right model{modelCandidates = Map.insert name found (modelCandidates model)}
            ["unigram", symbol, count] | Just found <- readText count -> Right model{modelUnigrams = Map.insertWith (+) symbol found (modelUnigrams model)}
            ["context", parent, position, symbol, count]
                | Just at <- readText position
                , Just found <- readText count ->
                    Right model{modelContexts = Map.insertWith (+) (parent, at, symbol) found (modelContexts model)}
            _ -> bad number line
    bad number line = Left ("fit-model: line " <> show number <> " is not a record: " <> Text.unpack line)
    readText :: (Read a) => Text -> Maybe a
    readText = readMaybe . Text.unpack
