{-# LANGUAGE OverloadedStrings #-}

{- | An order of fits by a decision model ("Decision"). The model reads a
description of the hole ('holeState') and gives a score to each fit of a
pool, in one question ('fitQuestion'); 'rankFits' puts the fits in the order
of their scores, and 'rankedFits' gives the order of a search's fits. The
model only orders fits that GHC has checked, so the fits stay exact. When
the model fails, the fits keep their own order.

The model runs on a server ("Decision.Ollama"), with the capability
"decision". The scores of a model that stays loaded depend on the requests
before them, so the default 'Ranking' asks the server to load the model for
each request: then each hole gets the same order each time.
-}
module Data.CFTA.GHC.Rank (
    -- * Rankings
    Ranking (..),
    defaultRanking,

    -- * Questions
    holeState,
    fitQuestion,

    -- * Orders
    rankFits,
    rankedFits,
) where

import Data.List (partition)
import Data.Text (Text)
import qualified Data.Text as Text
import Decision (DecisionModel (..), Option (..), Question (..), ranked)
import Decision.Ollama (Ollama (..), defaultOllama)

import Data.CFTA.GHC.Fits (Fit, comesLast)

-- | How a model ranks fits: the number of fits that it orders, and the server and the model.
data Ranking = Ranking
    { rankingPool :: Int
    , rankingServer :: Ollama
    }
    deriving (Eq, Show)

{- | A pool of 50 fits, and the model of 'defaultOllama' with the
'ollamaKeepAlive' @0@: the server loads the model for each request (about
4 s more for each request), so that no score depends on an earlier request.
-}
defaultRanking :: Ranking
defaultRanking = Ranking 50 defaultOllama{ollamaKeepAlive = "0"}

{- | The description of a hole: the name, the signature, and the arguments
of the definition with the hole, when there is one, the type of the hole,
and the local variables with their types.
-}
holeState :: Maybe (Text, Text, [Text]) -> Text -> [(Text, Text)] -> Text
holeState definition holeType locals =
    Text.unlines $
        ["A Haskell function has a typed hole:", ""]
            <> concat
                [ [name <> " :: " <> signature, Text.unwords (name : arguments) <> " = _", ""]
                | Just (name, signature, arguments) <- [definition]
                ]
            <> ["The hole has the type " <> holeType <> "."]
            <> [ "The local variables are " <> Text.intercalate ", " [local <> " :: " <> typ | (local, typ) <- locals] <> "."
               | not (null locals)
               ]
            <> ["", "Each candidate below typechecks in this scope."]

{- | The question about a pool of fits for a hole: which fit a programmer
most likely intends. Each program is an option, with its text as the name
and the description, so the programs must be different.
-}
fitQuestion :: Text -> [Text] -> Question
fitQuestion state programs =
    Question
        { questionName = "best_fit"
        , questionState = state
        , questionText = "Which candidate is the program that a Haskell programmer most likely intends for this hole?"
        , questionOptions = [Option program program | program <- programs]
        }

{- | The fits with their scores, in the order of the scores, the highest
first; fits with equal scores keep their order. The text of each fit is its
option. A failure of the model gives its message.
-}
rankFits :: DecisionModel -> Text -> (a -> Text) -> [a] -> IO (Either String [(a, Double)])
rankFits model state render fits = fmap (ranked fits) <$> scoreOptions model (fitQuestion state (map render fits))

{- | The fits of a search in the order of a model: the first fits that use
every part, as many as the pool, in the order of the model's scores; then
the other fits that use every part; and then the fits that come last
('comesLast'), each in their own order. A pool of one fit asks no question.
When the model fails, the fits keep their order, and the message comes
with them.
-}
rankedFits :: DecisionModel -> Text -> Int -> (Fit -> Text) -> [Fit] -> IO ([Fit], Maybe String)
rankedFits model state pool render fits
    | length pooled < 2 = pure (using <> later, Nothing)
    | otherwise = do
        answer <- rankFits model state render pooled
        pure $ case answer of
            Right scored -> (map fst scored <> rest <> later, Nothing)
            Left problem -> (using <> later, Just problem)
  where
    (using, later) = partition (not . comesLast) fits
    (pooled, rest) = splitAt pool using
