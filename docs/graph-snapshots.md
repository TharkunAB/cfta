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

## Validation results

The fresh all-component `-O0 -Werror` build, all six suites, Fourmolu, HLint,
cabal-gild, and package metadata checks pass. The file example saves and loads
in separate processes. It retains the recursive LTA and returns the expected
counts `[0,0,1,1,1]` and three terms through size five.

A standalone probe checks every formula, formula-term, sort, relation, and guard
constructor. It includes empty connectives, quantifiers, substitutions,
contradictory equalities, unusual text, and positive and negative 101-digit
integers. Complete graphs round-trip exactly, including empty, unreachable,
dead, duplicate, and cyclic rows. Ordinary, equality, and liquid size classes
retain their counts, ordered terms, and rank inverses through size seven.
The process that saves the files and two fresh readers produce the same output.
The readers create different sets of symbols before loading.

All 31 malformed-file checks pass. They include duplicate JSON keys, duplicate
states, graph errors, unknown fields and tags, malformed operands, exact integer
syntax, trailing data, and non-JSON trailing whitespace. Decoding errors identify
the document path or the invalid graph reference. The parser requires end of
input explicitly after valid JSON whitespace. The complete README program
compiles and prints `True`.

The eight standard benchmark cells keep their checksums against main
`c0cc8a05`. All six executables are byte-identical to main. Instruction
differences are below 0.11%; allocation differences are below 0.01%.

A separate `-O2` probe constructs a 10,000-state chain, encodes it, decodes it,
and compares the complete graphs. It uses the workspace dependency settings.
The JSON has 1,437,836 bytes. The complete probe takes 6,132,392,215 cachegrind
instructions, allocates 1,718,721,344 bytes, and reaches 28,086,344 bytes of
sampled maximum residency. The decoded graph has all 10,000 states.
This is a baseline for compact encoding and allocation work. It includes graph
construction and comparison; it is not a decode-only or index-reuse measurement.

Jobs run serially through heavy-management with 12 GiB process caps and 4 GiB
RTS caps. The text codec is a complete graph interchange path. It does not yet
meet the separate goal of a compact binary format or cheap repeated edits.
