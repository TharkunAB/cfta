{-# LANGUAGE NoImplicitPrelude #-}

{- | Qualified do-notation for the typing rules of "Data.CFTA.Gen.Typing".

Enable @QualifiedDo@ and import this module qualified. A block gives the rules
of one constructor, as an inference rule does: each bind is a premise or a
choice, and the last statement is the conclusion. A choice ('each') gives one
rule for each of its elements, so a block gives one rule for each combination
of its choices:

@
import qualified Data.CFTA.Gen.Typing.Do as Typing

letRules :: [Rule TypedNode Ty]
letRules = Typing.do
    rhs <- Typing.each [TInt, TBool]
    typ <- Typing.each [TInt, TBool]
    bound <- Typing.sub rhs
    body <- Typing.under [rhs] typ
    Typing.yields (TLetNode bound body) typ
@

A statement can read the values of the statements before it, as a divisor
reads its number, and 'guard' keeps only some combinations:

@
fractionRules :: [Rule FractionNode ()]
fractionRules = Typing.do
    n <- Typing.each [1 .. 12 :: Int]
    d <- Typing.each [1 .. n]
    Typing.guard (n \`mod\` d == 0)
    Typing.yields (FracNode (value n) (value d)) ()
@

A block is a list of rules, so blocks and other rules combine with '<>'. The
rules are built when the language is built: a block gives the same
automaton, counts, and ranks as the same rules in a list.
-}
module Data.CFTA.Gen.Typing.Do (
    -- * Statements
    each,
    sub,
    under,
    guard,
    yields,

    -- * The notation
    (>>=),
    (>>),
    return,
    pure,
    fmap,
    (<*>),
    join,
    fail,
) where

import Prelude (Bool, String, const, id)
import qualified Prelude

import qualified Control.Monad as Monad
import Data.CFTA.Gen.Typing (Child, Rule, rule, subterm)

-- | A choice of one element of the list: the block gives one rule for each element.
each :: [a] -> [a]
each = id

-- | A premise: a field that is a subterm of the type, in the environment of the node.
sub :: ty -> [Child ty]
sub typ = [subterm [] typ]

{- | A premise under binders: a field that is a subterm of the type, in the
environment of the node with the binders in front. The first binder is the
variable with the index 0 in the subterm.
-}
under :: [ty] -> ty -> [Child ty]
under binds typ = [subterm binds typ]

-- | Keep the combinations of the choices before it for which the condition holds.
guard :: Bool -> [()]
guard = Monad.guard

-- | The conclusion: the constructor of the node has the type when its fields are the children of the node.
yields :: node (Child ty) -> ty -> [Rule node ty]
yields node typ = [rule node typ]

-- | Bind a statement of a block.
(>>=) :: [a] -> (a -> [b]) -> [b]
(>>=) = (Prelude.>>=)

-- | Sequence two statements of a block.
(>>) :: [a] -> [b] -> [b]
(>>) = (Prelude.>>)

-- | A value as a statement of a block.
return :: a -> [a]
return = Prelude.return

-- | A value as a statement of a block.
pure :: a -> [a]
pure = Prelude.pure

-- | Map a statement of a block, for @ApplicativeDo@.
fmap :: (a -> b) -> [a] -> [b]
fmap = Prelude.fmap

-- | Apply a statement of a block, for @ApplicativeDo@.
(<*>) :: [a -> b] -> [a] -> [b]
(<*>) = (Prelude.<*>)

-- | Join a statement of a block, for @ApplicativeDo@.
join :: [[a]] -> [a]
join = Monad.join

-- | A bind whose pattern does not match gives no rule.
fail :: String -> [a]
fail = const []
