# Explicit automaton notation

Add an `automaton` expression quoter in `cfta-th`. Keep typing-rule notation
and EBNF as separate frontends. This notation describes the explicit graph
that `Data.CFTA.mkFTA` already accepts.

```haskell
[automaton|
start Expr;
Expr = $zero | "add"(Expr, Expr) where validAdd;
|]
```

A definition has one `start` declaration, then state rows. A row contains
alternatives separated by `|` and ends with `;`. A quoted label is an ordinary
symbol. `$name` refers to a Haskell `Symbol`, which can carry a refinement.
`where name` refers to a Haskell `Constraint`. Both references can be qualified.
A transition without a constraint uses `noConstraint`. Child states have the
written order. A transition without parentheses is nullary. `Empty = ;` is an
empty row. Line comments start with `--`. Strings use Haskell escapes.

Parse the quote at compile time. Check duplicate rows, the initial state,
child references, and arities of literal labels and repeated symbol names.
Resolve Haskell names and let GHC check their types. No Haskell expression
parser is required: bind a computed symbol or constraint outside the quote.

The expression has the type
`Either (FTAError String Symbol) (FTA String Symbol Constraint)`.
It calls `mkFTA` on the generated rows. Different symbol bindings can contain
the same symbol, so their final arities must be checked when the expression is
evaluated. Report that failure through `Either`. Constraint interpretation,
solver checks, recursion bounds, and counting stay in the existing APIs.
Cycles and empty languages remain valid.

## The file path

Expose a pure `parseAutomaton` for definitions with literal labels and no
named constraints. `parseAutomatonWith` also takes maps of symbol bindings and
constraint bindings. Both take a source name and the definition text, and
return a checked graph or a parse error with its source position. They share
the quote parser and structural checks. Unknown bindings fail at their use.
The parser module does not import Template Haskell.

Quote diagnostics use positions within the quote; GHC supplies its enclosing
source location. File diagnostics use the supplied file name. Preserve
alternative order. Do not add states, symbols, or predicate children.

## Validation

Compare quoted and file-parsed definitions with handwritten ordinary,
equality-constrained, and refined-symbol graphs. Check bounded terms, counts,
and ranks, including cycles and empty rows. Check malformed input, duplicate
rows, missing states, arity conflicts, unknown bindings, and aliasing symbol
bindings with conflicting arities. Compile a complete example. Use the normal
PR gate and the memory cap.

## Limits and follow-ups

Named bindings remain Haskell values; this text is not a self-contained
serialization format. The serialization and Lean-interchange TODOs must choose
how to store refinements and constraints. EBNF also needs a separate definition
of whether members are ASTs, derivations, or distinct strings. This quoter ranks
the same trees as the explicit graph builder.
