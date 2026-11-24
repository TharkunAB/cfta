{- | The mask of a prefix of a text: the characters that can come next, so
that the text stays the start of the text of an accepted term.

A 'Linearization' gives the texts of each symbol. The text of a term is the
texts of its symbol with the texts of its children between them
('linearize'). For example, the texts @["add(", ", ", ")"]@ of @add@ give the
text @add(one, two)@. 'textMask' gives the mask of the texts of a language
from the mask of its terms at the empty prefix
('Data.CFTA.Mask.completionsMask'): the 'Mask' of each prefix of the texts.
The mask of the texts reads the mask of the terms, so the constraints and the
solver of the language stay. A context-free grammar of the texts does not keep
them.

A reading of a text prefix is a prefix of term tokens with a place in its
text. The items that are still to come are the pending items of the reading.
A pending item is the rest of a text or a child that no token has started
yet. A reading is normal when its first pending item is a text that is not
empty, or when no item is pending. At a pending child, a reading becomes one
reading for each offered token of the mask of the terms. The mask of a text
prefix holds the normal readings of the prefix.

A text can be a whole term and can also continue: in a language of sums, the
text @1@ is a term, and the text @1 + 2@ continues it. Thus the mask offers
the explicit end token 'EndOfText' when a reading has no pending item, and
the scorer decides the end. The mask after 'EndOfText' has the terms of the
text in 'maskTerms'. Two terms can have one text, so this list can have more
than one term.

The probabilities are exact. Each term whose text starts with the prefix is a
completion of exactly one normal reading. The mass of a reading is the
product of the probabilities of its tokens in the mask of the terms. The
probability of a character is the mass of the readings after the character,
divided by the mass of the readings of the prefix. The probability of
'EndOfText' is the mass of the readings without a pending item, divided by
the same mass. When the linearization gives each token a text, the
probabilities of a prefix sum to one. The mask computes a mass only when a
caller reads a probability. It steps the mask of the terms after a token only
when a character selects the reading of the token, or when the first text of
the token is empty.

An undecided token of the mask of the terms makes the first character of its
first text undecided, when no reading offers that character. When the first
text of an undecided token is empty, the mask of the texts cannot see the
character after it. Then the mask refuses each token that it does not offer
with 'TokenUndecided'. The mask does not continue after an undecided token, so
it reads only the first character of its text.

Limit: a symbol whose first text is empty and whose first child can be the
same symbol again, such as an infix operator, gives one reading for each
depth of the left spine and each choice of the operators, up to the size
bound of the mask of the terms. Thus the number of readings can grow fast
with the bound. In a notation where each symbol starts with its own text,
such as a call notation, a prefix notation, or brackets around each child,
the readings do not grow in this way.
-}
module Data.CFTA.Mask.Text (
    Linearization,
    linearize,
    TextToken (..),
    textMask,
    TextError (..),
    readText,
) where

import Data.Either (fromRight)
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set

import Data.CFTA.Mask (Mask (..), Refusal (..))
import Data.CFTA.Sized.Prefix (Token)
import Data.CFTA.Term (Term (Node))

{- | The texts around the children of each symbol: the text before the first
child, the text between each two children, and the text after the last child.
A symbol with k children has k + 1 texts.
-}
type Linearization symbol = symbol -> [String]

-- | The text of a term. 'Nothing' when a node has not one more text than children.
linearize :: Linearization symbol -> Term symbol -> Maybe String
linearize texts (Node symbol children)
    | length pieces == length children + 1 =
        concat . zipWith (<>) pieces . (<> [""]) <$> traverse (linearize texts) children
    | otherwise = Nothing
  where
    pieces = texts symbol

-- | A token of a text: one character, or the end of the text.
data TextToken
    = -- | One character.
      Character Char
    | -- | The end of the text.
      EndOfText
    deriving (Eq, Ord, Show)

-- | An item that is still to come in a reading.
data Pending
    = -- | The rest of a text.
      Rest String
    | -- | A child that no token has started.
      Child

-- | A reading of a text prefix: a prefix of term tokens with a place in its text.
data Reading symbol term = Reading
    { readingMask :: Mask (Token symbol) term
    -- ^ The mask of the terms after the tokens of the reading.
    , readingMass :: Rational
    -- ^ The product of the probabilities of the tokens of the reading.
    , readingPending :: [Pending]
    -- ^ The pending items, the first item first.
    }

{- | The mask of the texts of a language, from the mask of its terms at the
empty prefix. The argument must be the mask of the empty prefix. A token
@(symbol, n)@ whose symbol has not @n + 1@ texts has no text, so the mask of
the texts does not offer it.

When the mask of the terms has an undecided token whose first text is empty,
the mask of the texts cannot see the next character. Then the step refuses
each token that the mask of the texts does not offer with 'TokenUndecided'.
-}
textMask :: Linearization symbol -> Mask (Token symbol) term -> Mask TextToken term
textMask texts start = prefixMask [] $ normal $ Reading start 1 [Child]
  where
    -- The pending items of a token: its texts with a pending child between each two.
    items (symbol, arity)
        | length pieces == arity + 1 = Just $ drop 1 $ concat [[Child, Rest piece] | piece <- pieces]
        | otherwise = Nothing
      where
        pieces = texts symbol
    -- The normal readings of a reading, and the first texts of the undecided tokens on the way.
    normal reading = case readingPending reading of
        Rest [] : rest -> normal reading{readingPending = rest}
        Child : rest ->
            foldMap (child reading rest) (maskNext mask)
                <> ([], [first | token <- maskUndecided mask, Just (Rest first : _) <- [items token]])
          where
            mask = readingMask reading
        _ -> ([reading], [])
    -- The normal readings after an offered token at a pending child. The step of an offered token is 'Right'.
    child reading rest (token, probability) = case items token of
        Nothing -> mempty
        Just pending ->
            normal
                Reading
                    { readingMask = fromRight (error "textMask: the mask refuses an offered token") $ maskStep (readingMask reading) token
                    , readingMass = readingMass reading * probability
                    , readingPending = pending <> rest
                    }
    prefixMask prefix normalized =
        Mask
            { maskPrefix = prefix
            , maskNext =
                [(Character character, share $ fst next) | (character, next) <- Map.toList normals]
                    <> [(EndOfText, share ended) | not $ null ended]
            , maskUndecided = undecidedCharacters
            , maskStep = step
            , maskTerms = []
            }
      where
        -- A pattern binding is lazy, so the mask normalizes its readings only when a caller reads a field.
        (readings, undecided) = normalized
        ended = [reading | reading@Reading{readingPending = []} <- readings]
        {- The normal readings after each character, with the first texts of the
        undecided tokens. The maps are lazy ("Data.Map.Lazy"), so the mask
        after a character normalizes its readings only when a caller reads it.
        -}
        normals =
            Map.map (foldMap normal) $
                Map.fromListWith
                    (flip (<>))
                    [ (character, [reading{readingPending = Rest rest : pending}])
                    | reading@Reading{readingPending = Rest (character : rest) : pending} <- readings
                    ]
        masks = Map.mapWithKey (\character -> prefixMask (prefix <> [Character character])) normals
        undecidedCharacters =
            map Character
                $ Set.toAscList
                $ Set.fromList [character | character : _ <- undecided] `Set.difference` Map.keysSet normals
        blind = any null undecided
        -- The divisor of each probability, computed once for all the tokens.
        total = sum $ map readingMass readings
        share group
            | total <= 0 = 0
            | otherwise = sum (map readingMass group) / total
        step token = case token of
            Character character | Just after <- Map.lookup character masks -> Right after
            EndOfText | not $ null ended -> Right $ endMask (prefix <> [EndOfText]) $ concatMap (maskTerms . readingMask) ended
            _
                | blind || token `elem` undecidedCharacters -> Left TokenUndecided
                | otherwise -> Left TokenRejected

-- | The mask after 'EndOfText': no next token, and the terms of the text.
endMask :: [TextToken] -> [term] -> Mask TextToken term
endMask prefix terms =
    Mask
        { maskPrefix = prefix
        , maskNext = []
        , maskUndecided = []
        , maskStep = const $ Left PrefixEnded
        , maskTerms = terms
        }

-- | Why a text is not the text of an accepted term.
data TextError = TextError
    { textErrorPlace :: Int
    -- ^ The number of characters before the refused token.
    , textErrorRefusal :: Refusal
    -- ^ The reason that the mask refuses the token.
    , textErrorExpected :: [TextToken]
    -- ^ The tokens that the mask offers at that place, in ascending order.
    }
    deriving (Eq, Show)

{- | The accepted terms that have this text. The function steps through the
'Character' of each character of the text, then through 'EndOfText'. At the
first refused token, the result is the place, the reason, and the offered
tokens.
-}
readText :: Mask TextToken term -> String -> Either TextError [term]
readText start text = go 0 start $ map Character text <> [EndOfText]
  where
    go _ mask [] = Right $ maskTerms mask
    go place mask (token : rest) = case maskStep mask token of
        Right after -> go (place + 1) after rest
        Left refusal -> Left $ TextError place refusal $ map fst $ maskNext mask
