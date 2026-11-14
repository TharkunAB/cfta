{- | The mask of the entries of a vocabulary: the entries that can come next,
so that their tokens continue the prefix of a mask below.

A vocabulary is a list of entries. An entry is a name with a list of tokens
of the mask below. The host chooses the names and gives the tokens of each
entry, so the library knows no tokenizer. For the vocabulary of a tokenizer,
the name of an entry is its number. Its tokens are the characters of its text
('Data.CFTA.Mask.Text.Character'), and one more entry has the token
'Data.CFTA.Mask.Text.EndOfText'.

'vocabularyMask' gives the 'Mask' of the entries from a mask of the tokens.
The tokens of the mask of the entries are the entries. It offers an entry
when the mask below steps through each token of the entry in order
('maskStep' gives 'Right' each time). The mask after the entry is the mask of
the entries over the mask below after the last token. An entry is undecided
when the mask below refuses one of its tokens with 'TokenUndecided' and steps
through each token before it. The mask below does not continue after an
undecided token, so the mask of the entries does not read the tokens after
it. It refuses each other entry with the refusal of its first refused token:
'PrefixEnded' when the mask below is ended, and 'TokenRejected' otherwise. It
refuses an entry that the vocabulary does not have with 'TokenRejected'. Two
entries with the same tokens are two entries, and the mask of the entries
offers both. Its 'maskTerms' is 'maskTerms' of the mask below. Thus after an
entry whose last token is 'Data.CFTA.Mask.Text.EndOfText', the mask of the
entries has the terms of the text.

The probability of an offered entry is the product of the probabilities of
its tokens. The mask of the entries reads the probability of each token from
'maskNext' of
the mask below at the step of the token. The product is the weight of the
completions after the entry, divided by the weight of the completions of the
prefix. Thus the value is the share of the completions that stay after the
entry. The offered entries are not disjoint events. When the tokens of one
entry are the start of the tokens of another entry, the mask of the entries
offers both entries, and the probabilities of a prefix can sum to more than
one. The mask computes a product only when a caller reads it. One sequence of tokens can be
the tokens of more than one sequence of entries, so a search can find one
term more than once.

The mask finds the offered and the undecided entries in one walk of a trie of
the entries along 'maskStep' of the mask below. Entries with a common start
share the steps of the common tokens. The walk visits only the nodes whose
tokens the mask below steps through. This walk of a trie is the usual method
of a constrained decoder for the vocabulary of a tokenizer. 'maskStep' of the
mask of the entries does not use the walk: it steps the mask below through
the tokens of the entry. 'Data.CFTA.Mask.Text.textMask' keeps the masks that a caller reached,
so these steps use the steps of the walk again.

An example: a language has the one term @add(one, two)@, with the texts
@["add(", ", ", ")"]@ of @add@ in 'Data.CFTA.Mask.Text.textMask'. A vocabulary
has the entries 0 for @add(@, 1 for @o@, 2 for @one@, 3 for @, @, 4 for @two@,
5 for @)@, and 6 for 'Data.CFTA.Mask.Text.EndOfText'. At the empty prefix, the
mask of the entries offers the entry 0 with the probability 1. After the entry
0, it offers the entries 1 and 2, each with the probability 1, so the
probabilities sum to 2. It refuses the entry 4 with 'TokenRejected'. After the
entries 0, 2, 3, 4, 5, and 6, the mask has the term in 'maskTerms', and it
refuses each entry with 'PrefixEnded'.
-}
module Data.CFTA.Mask.Vocabulary (
    Vocabulary,
    vocabulary,
    vocabularyMask,
) where

import Control.Monad (foldM)
import Data.List (sort, sortOn)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map

import Data.CFTA.Mask (Mask (..), Refusal (..))

-- | A node of the trie of a vocabulary: the entries that end at the node, and the node after each next token.
data Trie entry token = Trie
    { trieEntries :: [entry]
    -- ^ The entries whose last token leads to this node, in ascending order.
    , trieChildren :: Map token (Trie entry token)
    -- ^ The node after each next token.
    }

-- | The entries of a vocabulary, each with its tokens, arranged by their tokens.
data Vocabulary entry token = Vocabulary
    { vocabularyTrie :: Trie entry token
    -- ^ The trie of the tokens of the entries. The root has no entries.
    , vocabularyTokens :: Map entry [token]
    -- ^ The tokens of each entry.
    }

{- | The vocabulary of the entries, each with its tokens. When the list has an
entry more than once, the last tokens of the entry count.

The mask of the entries never offers an entry without tokens, and it refuses
the entry with 'TokenRejected'. A step with an entry without tokens does not change the
prefix of the mask below, so a search that takes such steps does not end.
-}
vocabulary :: (Ord entry, Ord token) => [(entry, [token])] -> Vocabulary entry token
vocabulary entries = Vocabulary (trie $ Map.toList tokens) tokens
  where
    tokens = Map.filter (not . null) $ Map.fromList entries

-- | The trie of the entries, each with its tokens. The entries must be in ascending order.
trie :: (Ord token) => [(entry, [token])] -> Trie entry token
trie entries =
    Trie
        { trieEntries = [entry | (entry, []) <- entries]
        , -- 'Map.fromListWith' puts the last entry first, so 'reverse' gives the ascending order again.
          trieChildren =
            Map.map (trie . reverse) $ Map.fromListWith (<>) [(token, [(entry, rest)]) | (entry, token : rest) <- entries]
        }

-- | The entries of a node and of each node below it.
entriesBelow :: Trie entry token -> [entry]
entriesBelow node = trieEntries node <> concatMap entriesBelow (Map.elems $ trieChildren node)

{- | The mask of the entries of a vocabulary, from a mask of their tokens.

The prefix of the mask of the entries is the list of the entries of its
steps, the first entry first. Thus the mask of the entries over a mask has the
empty prefix, whatever the prefix of the mask below is.
-}
vocabularyMask ::
    (Ord entry, Ord token) => Vocabulary entry token -> Mask token term -> Mask entry term
vocabularyMask Vocabulary{vocabularyTrie = root, vocabularyTokens = tokens} = entryMask []
  where
    entryMask prefix below =
        Mask
            { maskPrefix = prefix
            , maskNext = sortOn fst offered
            , maskUndecided = sort undecided
            , maskStep = \entry -> case Map.lookup entry tokens of
                Just entryTokens -> entryMask (prefix <> [entry]) <$> foldM maskStep below entryTokens
                Nothing -> Left TokenRejected
            , maskTerms = maskTerms below
            }
      where
        -- A pattern binding is lazy, so the mask walks the trie once, when a caller first reads a field.
        (offered, undecided) = walk below 1 root

{- | The offered entries below a node of the trie, each with its probability,
and the undecided entries below the node. The mask is the mask below after
the tokens of the node. The mass is the product of the probabilities of these
tokens.
-}
walk :: (Ord token) => Mask token term -> Rational -> Trie entry token -> ([(entry, Rational)], [entry])
walk mask mass node = foldMap child $ Map.toList $ trieChildren node
  where
    -- The map is lazy ("Data.Map.Lazy"), so it computes a probability only when a caller reads it.
    probabilities = Map.fromList $ maskNext mask
    child (token, next) = case maskStep mask token of
        Right after -> ([(entry, share) | entry <- trieEntries next], []) <> walk after share next
          where
            share = mass * Map.findWithDefault 0 token probabilities
        Left TokenUndecided -> ([], entriesBelow next)
        Left _ -> mempty
