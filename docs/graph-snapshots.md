# Self-contained graph snapshots

Add `Data.CFTA.Serialization.JSON` in the optional `cfta-serialization` package.
`encodeGraph` writes a `PlainFTA state Symbol` as UTF-8 JSON. `decodeGraph`
reads it and returns a checked graph or an error with a document path. State
values use the caller's `ToJSON` and `FromJSON` instances. Their round trip must
preserve state equality and ordering. Strings and integers are normal choices.

The format is `cfta-graph`, version 1. The top-level fields are `format`,
`version`, `initial`, and `states`. Each state has `state` and `transitions`.
Each transition has `symbol`, `children`, and `constraint`. A symbol has `text`
and `refinement`. A constraint has `equalities` and `guard`.

Rows, alternatives, children, and formula operands use arrays. Formula terms,
formulas, sorts, and guards use tagged arrays with a fixed number of operands.
Integer literals use decimal strings. Equality classes use arrays of paths;
`null` denotes `EqContradiction`. Preserve class order and formula syntax.
The complete schema belongs in the package README.

Decode with the standard duplicate-key-rejecting JSON parser from
`attoparsec-aeson`. Check fields and tags explicitly. Reject unknown fields,
duplicate state identities, malformed operands, unsupported format versions,
missing child states, and inconsistent symbol arities. Do not use derived
Haskell `Read` or silently accept a partial document. Decoding does not invoke
a solver, normalize formulas, trim rows, or intern the graph.

This snapshot preserves the explicit graph. It does not store named source
facts, host decoders, a query plan, a cursor, solver caches, or count tables.
Rebuild the same query route with the same ordering policy after loading.
A different query route or a graph edit can change ranks. Preserve duplicate
alternatives, empty rows, unreachable states, and cycles for the graph round
trip. Interned symbols and equality classes rebuild their local identities
from their contents.

The package keeps JSON dependencies out of the core packages. Use existing
Aeson instances for state values, with explicit codecs for the graph and its
constraints. Provide a complete executable that saves a constrained graph,
reads it back in another invocation, displays it, and queries it.

Validation must compare complete graphs and all formula/guard constructors,
including quantifiers, substitutions, empty connectives, negative and large
integers, and contradictory equalities. Check errors and trailing input.
Compare terms, counts, and ranks in separate processes for ordinary, equality,
and liquid graphs. Include a graph whose ranks change if a dead row is trimmed.
Use the normal strict build, suite, formatter, lint, and benchmark gates.
