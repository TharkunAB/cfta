{- | An automaton as a context-free grammar in the Lark syntax, for the
constrained decoders llguidance and XGrammar.

A linearization gives the text of a term. It gives each symbol the texts
around its children: one text before the first child, one text between each
two children, and one text after the last child. So a symbol with @k@
children has @k + 1@ texts, and a symbol without children has one text. The
text of a term is the texts of its symbol with the texts of its children
between them. 'linearize' gives the text of a term. For example, the texts
@["(", " + ", ")"]@ for @add@ give @(1 + 2)@ for @add(one, two)@.

'larkGrammar' gives a grammar that accepts exactly the texts of the terms
that the automaton accepts. Each state is a rule, and each transition of a
state is one alternative of its rule. The rules have the names @s0@, @s1@,
and so on, in the order of the states. The rule @start@ refers to the rule of
the initial state. The alternatives keep the order of the rows. So one
automaton and one linearization always give the same text.

The grammar uses only lowercase rule names, string literals, and @|@. Each
literal is in double quotes with JSON escapes. The XGrammar documentation
gives these escapes, and the string lexer of llguidance accepts them. The
grammar has no @%ignore@. The two engines ignore no text by default, so the
grammar accepts no white space that the texts do not contain. llama.cpp and
SGLang give a grammar to llguidance only when its first line is
@%llguidance {}@. Add that line for them.

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
express the empty language. A symbol without children must have a text that
is not empty ('EmptyText'): XGrammar documents an empty alternative, but
llguidance does not.
-}
module Data.CFTA.Lark (
    Linearization,
    LarkError (..),
    linearize,
    larkGrammar,
) where

import Data.Char (ord)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
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

-- | Why an automaton has no Lark grammar.
data LarkError symbol
    = -- | A transition of the automaton has a constraint.
      ConstrainedAutomaton
    | -- | The automaton accepts no term.
      EmptyLanguage
    | {- | The linearization gives a symbol a number of texts that is not one
      more than its arity: the symbol, its arity, and the number of texts.
      -}
      WrongTextCount !symbol !Arity !Int
    | -- | The linearization gives a symbol without children an empty text.
      EmptyText !symbol
    deriving (Eq, Show)

{- | The text of a term. 'Nothing' when the linearization gives a symbol of the
term a number of texts that is not one more than its arity.
-}
linearize :: Linearization symbol -> Term symbol -> Maybe String
linearize linearization (Term.Node symbol children)
    | length texts == length children + 1 = concat . weave texts <$> traverse (linearize linearization) children
    | otherwise = Nothing
  where
    texts = linearization symbol

{- | The Lark grammar of the texts of the terms that the automaton accepts.

The check for constraints reads every row of the automaton, also a row that
the initial state cannot reach. The check of the linearization reads only the
symbols of the trimmed automaton.
-}
larkGrammar :: (Ord state) => Linearization symbol -> FTA.PlainFTA state symbol -> Either (LarkError symbol) String
larkGrammar linearization automaton
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
        alternatives <- traverse alternative transitions
        pure $ name state <> ": " <> intercalate " | " alternatives
    alternative (FTA.Transition symbol children _)
        | length texts /= length children + 1 = Left $ WrongTextCount symbol (Arity $ length children) (length texts)
        | null children && all null texts = Left $ EmptyText symbol
        | otherwise = Right $ unwords $ filter (not . null) $ weave (map literal texts) (map name children)
      where
        texts = linearization symbol

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
