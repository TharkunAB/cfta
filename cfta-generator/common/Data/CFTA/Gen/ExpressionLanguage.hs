{- | Expressions over two atoms: a fixture language with an equality
constraint and an exclusion.

The states are @E@, an expression, and @A@, an atom. The symbols are
characters:

* @a@ and @b@ are the atoms.
* @(@ has one child at @E@: an expression in parentheses.
* @+@ and @*@ are operators with an expression on the left and an atom on
  the right: the children @[E, A]@.

Both states have the atoms and the parentheses. Only @E@ has the operators.
'structuralAutomaton' has these terms. Two automata restrict them:

* 'equalAutomaton' adds an equality constraint to @+@: the two children of
  @+@ are equal terms. Thus @+(a, a)@ is a term of 'equalAutomaton', and
  @+(a, b)@ is not.
* 'singleParenthesesAutomaton' excludes double parentheses: parentheses
  directly around parentheses ('excludeAnywhereFTA'). Thus @(a)@ is a term
  of 'singleParenthesesAutomaton', and @((a))@ is not.

The fixture has two restricted languages because they use two routes of
"Data.CFTA.Sized.Prefix". The equality is a constraint, and an export of the
language to a context-free grammar drops it. With a constraint, the
completions of a prefix are a list of terms. The exclusion keeps the
automaton ordinary: it has no constraint, so the completions read the size
index.
-}
module Data.CFTA.Gen.ExpressionLanguage (
    structuralAutomaton,
    equalAutomaton,
    singleParenthesesAutomaton,
) where

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Path (path)
import Data.CFTA.Template (Obligation, Template (..), excludeAnywhereFTA)

-- | The expressions without a constraint.
structuralAutomaton :: FTA.PlainFTA Char Char
structuralAutomaton = expressions False

-- | The expressions in which the two children of each @+@ are equal.
equalAutomaton :: FTA.PlainFTA Char Char
equalAutomaton = expressions True

-- | The expressions without double parentheses: no subterm matches @((_))@.
singleParenthesesAutomaton :: FTA.PlainFTA (Char, Obligation Char) Char
singleParenthesesAutomaton = excludeAnywhereFTA [TemplateNode '(' [TemplateNode '(' [Hole]]] structuralAutomaton

-- | The expressions, with the equality on @+@ when the argument is 'True'.
expressions :: Bool -> FTA.PlainFTA Char Char
expressions equal =
    either (error . ("invalid expression FTA: " <>) . show) id $
        FTA.mkFTA 'E' [('E', atoms <> operators), ('A', atoms)]
  where
    atoms = [FTA.Transition atom [] noConstraint | atom <- "ab"] <> [FTA.Transition '(' "E" noConstraint]
    operators = [FTA.Transition operator "EA" (constraint operator) | operator <- "+*"]
    constraint operator
        | equal && operator == '+' = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
        | otherwise = noConstraint
