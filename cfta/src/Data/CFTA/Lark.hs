{- | An automaton as a context-free grammar in the Lark syntax, for the
constrained decoders llguidance and XGrammar.

A linearization gives the text of a term. It gives each symbol the texts
around its children: one text before the first child, one text between each
two children, and one text after the last child. So a symbol with @k@
children has @k + 1@ texts, and a symbol without children has one text. The
text of a term is the texts of its symbol with the texts of its children
between them. 'linearize' gives the text of a term. For example, the texts
@["(", " + ", ")"]@ for @add@ give @(1 + 2)@ for @add(one, two)@.

A linearization by state ('StateLinearization') gives the texts by the state
and the symbol of each transition, so one symbol can have other texts in
another state: for example @cons@ with a line feed in a list of lines, and
with a space in a list of words. The text of a term then depends on its run:
'linearizeRun' gives the text of the first run of the automaton.
'everyState' gives each state the texts of a linearization.

A linearization by state can also give a state brackets: pairs of an opening
and a closing text. Each pair adds an alternative without a symbol to the rule
of the state: the opening text, the state, and the closing text. Text in
brackets has the term of the text inside, so a term has more than one text:
@1 + 2@, @(1 + 2)@, and @((1 + 2))@ are texts of one term. A parse of a text
gives a tree with bracket nodes, and the term is the tree without them. So a
parse back is unique up to brackets when the linearization without brackets
keeps the terms apart. Brackets also let a linearization without them, such
as @1 + 2 + 1@ for two sums, have texts that tell its terms apart. The grammar
still accepts the ambiguous text, so a parse back of that text chooses one
term. 'linearizeRun' gives the text without brackets.

'larkGrammar' and 'larkGrammarByState' give a grammar that accepts exactly the
texts of the terms that the automaton accepts. Each state is a rule, and each
transition of a state is one alternative of its rule, then each pair of
brackets. The rules have the names @s0@, @s1@, and so on, in the order of the
states. The rule @start@ refers to the rule of the initial state. The
alternatives keep the order of the rows. So one automaton and one
linearization always give the same text.

The grammar uses only lowercase rule names, string literals, and @|@. Each
literal is in double quotes with JSON escapes. The XGrammar documentation
gives these escapes, and the string lexer of llguidance accepts them. The
grammar has no @%ignore@. The two engines ignore no text by default, so the
grammar accepts no white space that the texts do not contain. llama.cpp and
SGLang give a grammar to llguidance only when its first line is
@%llguidance {}@. Add that line for them.

An empty text gives no literal, so a symbol without children and with the
empty text gives an empty alternative. Lark 1.3.1 and llguidance 1.9.1 accept
an empty alternative at the start, in the middle, and at the end of a rule,
and a rule whose only alternative is empty. Lark refuses the literal @""@,
which the grammar never has. The XGrammar documentation gives an empty
alternative too.

Two terms can have the same text. Then the grammar accepts the text, but a
parse of the text cannot tell the two terms apart. This module does not check
for that. The caller chooses a linearization that keeps terms apart, for
example with parentheses around each child.

A grammar cannot express a constraint: an equality between two subterms, or
a guard. A transition with a constraint gives 'ConstrainedAutomaton'. The
module does not remove the constraints, because 'FTA.dropConstraints' is the
explicit over-approximation. To export the over-approximation, apply
'FTA.dropConstraints' first.

'larkGrammar' trims the automaton first ('FTA.trim'). In Lark, a rule without
alternatives accepts the empty text, not no text. When the automaton accepts
no term, the result is 'EmptyLanguage', because rules and literals cannot
express the empty language. A pair of brackets with two empty texts would add
an alternative that is the state itself, so it gives 'EmptyBrackets'.
-}
module Data.CFTA.Lark (
    Linearization,
    StateLinearization (..),
    LarkError (..),
    everyState,
    linearize,
    linearizeRun,
    larkGrammar,
    larkGrammarByState,
) where

import Control.Monad (zipWithM)
import Data.Char (ord)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Text.Printf (printf)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Index (Arity (..))
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

{- | The texts around the children of each symbol: the text before the first
child, the text between each two children, and the text after the last
child.
-}
type Linearization symbol = symbol -> [String]

-- | The texts of each symbol in each state, and the brackets of each state.
data StateLinearization state symbol = StateLinearization
    { stateTexts :: state -> symbol -> [String]
    -- ^ The texts around the children of a symbol in a state.
    , stateBrackets :: state -> [(String, String)]
    -- ^ The opening and the closing text of each pair of brackets of a state.
    }

-- | Why an automaton has no Lark grammar.
data LarkError state symbol
    = -- | A transition of the automaton has a constraint.
      ConstrainedAutomaton
    | -- | The automaton accepts no term.
      EmptyLanguage
    | {- | The linearization gives a symbol in a state a number of texts that
      is not one more than its arity: the state, the symbol, its arity, and
      the number of texts.
      -}
      WrongTextCount !state !symbol !Arity !Int
    | -- | A pair of brackets of the state has two empty texts.
      EmptyBrackets !state
    deriving (Eq, Show)

-- | The texts of a linearization in each state, without brackets.
everyState :: Linearization symbol -> StateLinearization state symbol
everyState texts = StateLinearization (const texts) (const [])

{- | The text of a term. 'Nothing' when the linearization gives a symbol of the
term a number of texts that is not one more than its arity.
-}
linearize :: Linearization symbol -> Term symbol -> Maybe String
linearize linearization (Term.Node symbol children)
    | length texts == length children + 1 = concat . weave texts <$> traverse (linearize linearization) children
    | otherwise = Nothing
  where
    texts = linearization symbol

{- | The text of a term in the first run of the automaton from its initial
state, without brackets: the transitions of each state in the order of the
rows. 'Nothing' when the automaton does not accept the term, or when the
linearization gives a symbol of the run a number of texts that is not one
more than its arity.
-}
linearizeRun ::
    (Ord state, Eq symbol) => StateLinearization state symbol -> FTA.PlainFTA state symbol -> Term symbol -> Maybe String
linearizeRun linearization automaton = textIn $ FTA.initialState automaton
  where
    textIn state (Term.Node symbol children) =
        listToMaybe
            [ concat $ weave texts childTexts
            | FTA.Transition symbol' childStates _ <- FTA.transitionsFrom automaton state
            , symbol' == symbol
            , length childStates == length children
            , let texts = stateTexts linearization state symbol
            , length texts == length children + 1
            , Just childTexts <- [zipWithM textIn childStates children]
            ]

-- | The Lark grammar of the texts of the terms that the automaton accepts, with the same texts in each state.
larkGrammar ::
    (Ord state) => Linearization symbol -> FTA.PlainFTA state symbol -> Either (LarkError state symbol) String
larkGrammar = larkGrammarByState . everyState

{- | The Lark grammar of the texts of the terms that the automaton accepts, with
the texts and the brackets of each state.

The check for constraints reads every row of the automaton, also a row that
the initial state cannot reach. The check of the linearization reads only the
states and the symbols of the trimmed automaton.
-}
larkGrammarByState ::
    (Ord state) => StateLinearization state symbol -> FTA.PlainFTA state symbol -> Either (LarkError state symbol) String
larkGrammarByState linearization automaton
    | any (any ((/= noConstraint) . FTA.transitionConstraint)) (FTA.transitionTable automaton) = Left ConstrainedAutomaton
    | null (FTA.transitionsFrom trimmed (FTA.initialState trimmed)) = Left EmptyLanguage
    | otherwise = do
        rules <- traverse rule (Map.toList $ FTA.transitionTable trimmed)
        pure $ unlines $ ("start: " <> name (FTA.initialState trimmed)) : rules
  where
    trimmed = FTA.trim automaton
    numbers = Map.fromList $ zip (FTA.states trimmed) [0 :: Int ..]
    name state = "s" <> show (numbers Map.! state)
    rule (state, transitions) = do
        alternatives <- traverse (alternative state) transitions
        brackets <- traverse (bracket state) $ stateBrackets linearization state
        pure $ name state <> ": " <> intercalate " | " (alternatives <> brackets)
    alternative state (FTA.Transition symbol children _)
        | length texts /= length children + 1 = Left $ WrongTextCount state symbol (Arity $ length children) (length texts)
        | otherwise = Right $ unwords $ filter (not . null) $ weave (map literal texts) (map name children)
      where
        texts = stateTexts linearization state symbol
    bracket state (opening, closing)
        | null opening && null closing = Left $ EmptyBrackets state
        | otherwise = Right $ unwords $ filter (not . null) [literal opening, name state, literal closing]

-- | The first text, the first child, the second text, and so on.
weave :: [a] -> [a] -> [a]
weave (text : texts) (child : children) = text : child : weave texts children
weave texts [] = texts
weave [] children = children

{- | A text as a Lark string literal with JSON escapes. The empty text gives
the empty string, so that the alternative leaves it out.
-}
literal :: String -> String
literal "" = ""
literal text = "\"" <> concatMap escape text <> "\""
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape character
        | ord character < 0x20 || ord character == 0x7f = printf "\\u%04x" (ord character)
        | otherwise = [character]
