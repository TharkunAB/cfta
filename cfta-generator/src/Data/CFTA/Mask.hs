{- | The mask of a prefix: the tokens that can come next after the prefix, and
the step after each of them.

A 'Mask' value is the mask of one prefix of one language. It gives the
prefix, the offered tokens with their probabilities, the undecided tokens,
the mask after a token, and the accepted terms that the prefix is.
'completionsMask' gives the mask of each prefix of a 'Completions' value of
"Data.CFTA.Sized.Prefix". Its tokens are the tokens of the terms in preorder.

A complete prefix of the tokens of a term is one term, and no token can come
next. A mask that is made from another mask can give a prefix that is
complete and can also continue. Thus 'maskTerms' is a list, and such a mask
offers an explicit end token.

An undecided token is neither offered nor rejected: 'maskStep' refuses it
with 'TokenUndecided'. A caller that continues after an undecided token uses
the 'Completions' value directly
('Data.CFTA.Sized.Prefix.afterToken').
-}
module Data.CFTA.Mask (
    Mask (..),
    completionsMask,
    Refusal (..),
) where

import Data.CFTA.Sized.Prefix (
    Completions,
    Refusal (..),
    Token,
    completionPrefix,
    completionTerms,
    completionWeight,
    isComplete,
    nextTokenWeights,
    stepToken,
    undecidedTokens,
 )
import Data.CFTA.Term (Term)

-- | The mask of a prefix of one language: the tokens that can come next, and the step after each of them.
data Mask token term = Mask
    { maskPrefix :: [token]
    -- ^ The prefix, the first token first.
    , maskNext :: [(token, Rational)]
    {- ^ The offered tokens, in ascending order, each with its probability under
    the weights of the completions: the weight of the completions after the
    token, divided by the weight of the completions of the prefix. Each
    probability is computed only when a caller reads it.
    -}
    , maskUndecided :: [token]
    -- ^ The undecided tokens, in ascending order. They are not offered.
    , maskStep :: token -> Either Refusal (Mask token term)
    {- ^ The mask after an offered token, or the reason that the token is not
    offered. The prefix of the result is the prefix with the token at the end.
    -}
    , maskTerms :: [term]
    -- ^ The accepted terms that the prefix is. Empty when the prefix is not complete.
    }

{- | The mask of the prefix of a 'Completions' value. The offered tokens are
the tokens of 'Data.CFTA.Sized.Prefix.nextTokens', each with its
'Data.CFTA.Sized.Prefix.tokenProbability', or zero when the completions have
the weight zero. The undecided tokens are the tokens of 'undecidedTokens'.
'maskStep' is 'stepToken'. 'maskTerms' has the term of the prefix when the
prefix is complete ('isComplete').

The probabilities use the weights of the 'Completions' value. Apply
'Data.CFTA.Sized.Prefix.withWeights' before 'completionsMask' to give other
weights. Without it, each symbol has the weight one, so a probability is the
number of the completions after the token, divided by the number of the
completions of the prefix.
-}
completionsMask :: (Ord symbol) => Completions symbol -> Mask (Token symbol) (Term symbol)
completionsMask completions =
    Mask
        { maskPrefix = completionPrefix completions
        , maskNext = [(token, probability weight) | (token, weight) <- nextTokenWeights completions]
        , maskUndecided = map fst $ undecidedTokens completions
        , maskStep = fmap completionsMask . stepToken completions
        , maskTerms = if isComplete completions then take 1 $ completionTerms completions else []
        }
  where
    -- The divisor of each probability, computed once for all the tokens.
    total = completionWeight completions
    probability weight
        | total <= 0 = 0
        | otherwise = weight / total
