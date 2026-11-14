{- | The scorer of a trained model. A guided search with this scorer needs no
outside model. "Data.CFTA.Guided" does not import the model, so the search
depends only on the mask.
-}
module Data.CFTA.Guided.Model (
    modelScorer,
) where

import Data.CFTA.Guided (Scorer)
import Data.CFTA.Sized.Prefix (Token)
import Data.CFTA.Sized.Prefix.Model (Model, nextTokenProbabilities)

{- | The scorer of a trained model: the score of a token is the log of its
probability after the prefix, as 'nextTokenProbabilities' gives it. When no
completion of the model starts with the prefix, the scorer gives no score, so
the search gives each offered token the score minus infinity and ends at a
dead end. A token with the probability zero has the score minus infinity, and
the search does not write it.
-}
modelScorer :: (Ord symbol) => Model symbol -> Scorer (Token symbol)
modelScorer model prefix = pure $ maybe [] (map (fmap log)) $ nextTokenProbabilities model prefix
