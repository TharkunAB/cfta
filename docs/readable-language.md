# Readable language values

Provide one pure printer and parser in `Data.CFTA.Serialization.Text`. The
printed form must retain the complete `Language state` value. Parsing it must
return that exact value, including source identities, individual facts, raw
constraint syntax, source transition order, empty and unreachable rows, cycles,
full refinements, and named root or subtree exclusions. The state codec must
preserve equality and ordering, as for JSON snapshots.

The law is `parseLanguage (printLanguage value) == Right value`. Printing a
parsed canonical representation must reproduce that representation. Whitespace
and `//` line comments are presentation. The parser accepts them, but the
printer does not retain them. Thus the bijection is between language values
and canonical text, not every possible spelling of the input.

Use this surface for the concrete language example:

```text
language 1;
start Expr;

state Atom {
  zero = zero @{ v == 0 };
  one = one @{ v == 1 };
  two = two @{ v == 2 };
}

state Expr {
  pair = pair(Atom, Atom) {
    same = equal([0], [1]);
  };
  wrap = wrap(Expr);
}

exclude zero-pair = root pair(zero @{ v == 0 }, zero @{ v == 0 });
```

State values that encode as JSON strings use identifiers or JSON-quoted strings.
Other state shapes use `json(VALUE)`. Production, fact, exclusion, and symbol
names use identifiers or quoted strings. Names start with an ASCII letter or
underscore and continue with ASCII letters, digits, underscores, or hyphens.
The printer quotes `_` and `json`. The former is a template hole; the latter
introduces a complete JSON state value.

A production gives its name, symbol, ordered child state references, and optional
named facts. A symbol can have an explicit refinement after `@{ ... }`. The
printer omits only an exact `Top` refinement. Simple value comparisons use `v`
for the library's distinguished refinement value and an integer literal on the
right. Support all six relations, `true`, `false`, and `raw JSON` for every
other formula. Do not normalize formulas when choosing a printed form.

Facts use `true`, `false`, `impossible`, `equal(PATH, ...)`, or
`satisfies(PATH, FORMULA)` when those forms reproduce the exact constraint.
`equal` represents exactly one stored equality class, including an empty or
singleton class. `impossible` denotes equality contradiction with a top guard;
`false` denotes a bottom guard with no equality classes. All other constraints
use `raw JSON`, with the complete existing constraint schema. Paths are arrays
of child indices. Preserve non-normalized guards and equality classes.

An exclusion has an explicit `root` or `anywhere` scope. Templates use `_` for
a hole, `f(a, b)` for an exact node, `_(a, b)` for an arbitrary root with exactly
those children, and a final `...` for a prefix. Empty prefixes remain distinct
from leaves. Templates retain complete refined symbols.

Move shared JSON value codecs to a package-internal module. Keep the public
JSON API and its stored formats unchanged. The text parser constructs the same
complete value representation and uses the same graph and document validation.
Reject duplicate facts and exclusions before building maps. Keep duplicate
source rows and production names visible to the document validator. Use the
existing attoparsec dependency. No imports, host bindings, or evaluation occur
while parsing. Return line and column for syntax errors and existing source
identities or paths for schema errors.

Add a complete text save, reopen, inspect, update, and save example. Updates
still use the typed language API; editing a file is not required. Use the same
parser for a future quasiquoter. Do not add a separate quote semantics here.

Verify exact value and canonical-text round trips for all formula, guard, and
template forms, refined symbols, unusual names, generic state shapes, raw
non-normalized constraints, empty rows, repeated alternatives, and recursion.
Check malformed syntax, duplicate names, bad source references, unknown versions,
and exact errors. Reopen in independent processes and compare ranks. Recheck all
JSON codecs after moving their helpers, including unchanged stored bytes.
Measure text size, parse/print allocation and instructions, and the existing
JSON path. Use the normal capped build, format, test, and benchmark gates.

## Prior art and boundary

Derived Haskell `Read` and `Show` require suitable component instances. The
current symbol reader only accepts plain text, while its printer also emits
refined symbols. Formula and guard types have no `Read` instance. Direct record
output also exposes much more structure than the grammar example needs.
See the [Haskell report](https://www.haskell.org/onlinereport/haskell2010/haskellch11.html).

[KDL](https://kdl.dev/spec/) provides typed nodes and ordered children, but still
needs a language-specific representation for the constraints and references.
[Dhall's syntax encoding](https://github.com/dhall-lang/dhall-lang/blob/master/standard/binary.md)
is separate from normalization. Preserve source syntax here as well; semantic
normalization cannot serve as the identity of an editable definition. The small
grammar surface reuses this package's existing complete schema and dependencies.

The [prior-art comparison](language-authoring-prior-art.md) covers Redex,
syntax-spec, S-expressions, EDN, KDL, JSON5, and Hjson. It gives concrete mappings,
Haskell implementation findings, and independent authoring follow-ups.
