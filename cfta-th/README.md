# cfta-th

Generate a scalar node view from a datatype, or quote an explicit automaton.
The node view removes the duplicate constructor and field declarations used by
typing rules and refinement invariants. Template Haskell stays in this optional
package.

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
validation plan.

## Quote an automaton

`automaton` quotes an explicit graph. The quote is the graph format of
[cfta-serialization](../cfta-serialization/README.md) without its `graph 1;`
line, so a quote and a saved graph use one syntax:

```haskell
{-# LANGUAGE QuasiQuotes #-}

import Data.CFTA (PlainFTA)
import Data.CFTA.Serialization.Text (TextError)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.TH (automaton)

-- equalChildren :: Constraint and zero :: Symbol are defined elsewhere.
pairs :: Either (TextError String) (PlainFTA String Symbol)
pairs =
    [automaton|
        start Pair;
        state Pair { pair(Atom, Atom) where $equalChildren; }
        state Atom { $zero; one @{ v == 1 }; }
    |]
```

`$name` takes the place of a symbol, and `where $name` the place of a
constraint. The name is a Haskell `Symbol` or `Constraint` in scope, and can be
qualified. The quote checks its syntax, its names, and its state rows at
compile time, and GHC checks the types of the named values. Two names can hold
the same symbol, so `mkFTA` checks the symbol arities when the expression is
evaluated, and the result is an `Either`.

The quote is read again with the named values when the expression is
evaluated. Without names, the result is the same as `parseGraph` of the text
with the `graph 1;` line. `parseGraphQuote` in `cfta-serialization` reads a
quote from a file, with the values of its names in two maps.
