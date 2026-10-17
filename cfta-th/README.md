# cfta-th

Generate a scalar node view from a datatype, or quote an explicit automaton.
The node view removes the duplicate
constructor and field declarations used by typing rules and refinement
invariants. Template Haskell stays in this optional package.

```haskell
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}

module Arithmetic where

import GHC.Generics (Generic)
import Data.CFTA.Generic (HasFTA)
import Data.CFTA.Gen.Typing
import Data.CFTA.TH (deriveNode)

data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

$(deriveNode ''Expr)

data Ty = TInt deriving (Eq, Ord, Show)

rules :: [Rule ExprNode Ty]
rules =
    [ rule (LitNode (value (0 :: Int))) TInt
    , rule (LitNode (value (1 :: Int))) TInt
    , rule (AddNode (subterm [] TInt) (subterm [] TInt)) TInt
    ]
```

The splice declares `ExprNode e = LitNode e | AddNode e e`, derives `Generic`,
and declares a `NodeView` instance. Use `Typing (Nesting 2) [] [TInt] rules`
with the existing generator API. In this example, the two literal values
are the complete literal domain. The result has 38 terms.

Append `Node` to the source type and constructor names. Keep constructor order
and field count. Record fields become positional fields. Each field becomes
`e`; source type parameters do not become parameters of the view. A newtype
also gives a node datatype. Names already in scope are reported at the splice.

Enable `TemplateHaskell` and `DeriveGeneric`. Put the splice after the source
declaration and before the rules that use its view. The view is regenerated
when the source declaration changes. The existing requirements on `HasFTA`
and on recursive fields still apply. Empty datatypes also need
`EmptyDataDeriving` for the generated instance.

GADTs, existential or constrained constructors, datatype contexts, symbolic
names, type synonyms, and data families need a manual view. A view with a
record of measures also remains manual. This package generates scalar views;
it does not change term types, constraints, counts, or ranks.

See the [design note](../docs/generated-node-views.md) for the boundary and
validation results.

## Quote an automaton

This complete program counts the natural-number term with four nodes:

```haskell
{-# LANGUAGE QuasiQuotes #-}

module Main (main) where

import qualified Data.CFTA.Sized as Sized
import Data.CFTA.TH (automaton)

main :: IO ()
main = do
    graph <- either (fail . show) pure [automaton|
        start N;
        N = "zero" | "succ"(N);
    |]
    sizes <- either (fail . show) pure (Sized.sized graph)
    print (Sized.countOfSize sizes 4)
```

The quote returns the same `Either` result as `Data.CFTA.mkFTA`. It retains
the written alternative and child orders. Cycles are valid; bound them when
you enumerate or sample. `Empty = ;` declares a state with no alternatives.
Use `--` for a line comment and Haskell escapes inside quoted labels.

Use `$name` instead of a quoted label to refer to a Haskell `Symbol`, including
a refined symbol. Add `where name` to refer to a Haskell `Constraint`.
Both names can be qualified. For example:

```haskell
[automaton|
start Pair;
Pair = "pair"(Atom, Atom) where samePositive;
Atom = $zero | $one;
|]
```

See [QuotedAutomaton.hs](examples/QuotedAutomaton.hs) for the complete example,
including the refined symbols and the equality and semantic constraints.
Run it from the workspace with `cabal run cfta-quoted-automaton`.

The quote checks state names, duplicate rows, child references, known arities,
and Haskell binding names at compile time. GHC checks binding types. Two
different bindings can hold the same symbol, so `mkFTA` also checks the final
arities at runtime. Constraint interpretation stays in the existing engine.

## Read the same syntax from a file

`Data.CFTA.Syntax.Automaton.parseAutomaton sourceName contents` reads a graph
with literal labels and no named constraints. `parseAutomatonWith sourceName
symbols constraints contents` also takes a `Map String Symbol` and a
`Map String Constraint` for the named bindings. Both functions return a checked
graph or an error with a source position. Neither function starts a solver.
The parser module does not import Template Haskell.

Named bindings are external values, so this notation is not a self-contained
serialization format. Typing-rule and EBNF notations remain separate work.
See the [quoter design](../docs/automaton-quoter.md) for the checking boundary.
