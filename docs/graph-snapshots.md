# Self-contained graph snapshots

`Data.CFTA.Serialization.Text` in the optional `cfta-serialization` package
prints and parses complete `PlainFTA state Symbol` values. The `graph 2;` format
retains rows, alternatives, children, refinements and every constraint constructor.
A parser checks duplicate state identities, references and symbol arities before
constructing the graph. Errors give a syntax location or a typed source error.

State labels use lawful `Show`/`Read` instances or an explicit `StateCodec`.
The codec must preserve state equality and ordering. Logic syntax is encoded
explicitly; it does not depend on the core types having `Read` instances.
No solver, normalization, trimming or graph interning runs while parsing.

The format retains duplicate alternatives, empty rows, unreachable states and
cycles. It does not store source fact provenance, host functions, a query plan,
cursors, solver caches or count tables. Rebuild the same query route and ordering
after loading. Graph edits or a different query route can change ranks.

See the [complete syntax](../cfta-serialization/README.md) and the
[JSON-removal specification](complete-readable-language.md). The previous JSON
codec and its dependencies have been removed. The measurements below document
its historical baseline; current text validation and cost belong in the latter
specification.

## Historical JSON baseline (PR #74)

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
