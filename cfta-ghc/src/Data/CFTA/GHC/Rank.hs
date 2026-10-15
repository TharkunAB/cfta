{-# LANGUAGE OverloadedStrings #-}

{- | An order of fits by a decision model ("Decision"). The model reads a
description of the hole ('holeState') and gives a score to each fit of a
pool, in one question ('fitQuestion'); 'rankFits' puts the fits in the order
of their scores. The model only orders fits that GHC has checked, so the fits
stay exact. When the model fails, the caller keeps its own order.
-}
module Data.CFTA.GHC.Rank (
    holeState,
    fitQuestion,
    rankFits,
) where

import Data.Text (Text)
import qualified Data.Text as Text
import Decision (DecisionModel (..), Option (..), Question (..), ranked)

{- | The description of a hole: the name and the signature of the
definition, its equation with the hole, the type of the hole, and the local
variables with their types.
-}
holeState :: Text -> Text -> [Text] -> Text -> [(Text, Text)] -> Text
holeState name signature arguments holeType locals =
    Text.unlines $
        [ "A Haskell function has a typed hole:"
        , ""
        , name <> " :: " <> signature
        , Text.unwords (name : arguments) <> " = _"
        , ""
        , "The hole has the type " <> holeType <> "."
        ]
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
