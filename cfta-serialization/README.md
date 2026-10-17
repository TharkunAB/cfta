# cfta-serialization

Read and write self-contained explicit automata. The JSON format stores symbols,
refinements, equality classes, guards, states, and transitions. It retains cycles,
empty states, unreachable rows, repeated alternatives, and child order.

Use `Data.CFTA.Serialization.JSON.encodeGraph` and `decodeGraph`. State values
use their Aeson instances. Their round trip must preserve equality and ordering.
Decoding returns `InvalidDocument` with a JSON path or `InvalidGraph` with the
structural error. It does not run a solver or enumerate terms.

The format is `cfta-graph`, version 1. A graph snapshot does not contain named
source facts, host functions, a query plan, a cursor, or count caches. Use the
same query route and ordering policy after loading to retain ranks.

For editable languages, use [composable updates](#compose-updates-to-a-language-value)
and [readable exact definitions](#readable-definitions-with-exact-round-trips).
Change the language value through typed expressions, then save it. The graph
snapshot API below also supports callers that already have a compiled automaton.

## Save, reopen, inspect, and query

From the workspace, run these commands in separate processes:

```sh
cabal run cfta-graph-snapshot -- save /tmp/language.json
cabal run cfta-graph-snapshot -- load /tmp/language.json
python3 -m json.tool /tmp/language.json
```

The example saves equal positive pairs and recursive `wrap` terms. Loading
prints a finite graph view with its full annotations. It then uses Z3 to rebuild
size classes through five nodes. The counts are `[0,0,1,1,1]`. The terms are
`pair(one,one)`, `wrap(pair(one,one))`, and `wrap(wrap(pair(one,one)))`.
Saving does not need Z3. The example writes a temporary file, closes it, then
renames it over the target. It does not promise durability across power loss.

This complete program performs a graph round trip without a solver:

```haskell
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Serialization.JSON (decodeGraph, encodeGraph, explainDecodeError)
import Data.CFTA.Symbol (Symbol)

main :: IO ()
main = do
    graph <- either (fail . show) pure $ FTA.mkFTA ("N" :: String)
        [("N", [FTA.Transition ("zero" :: Symbol) [] noConstraint,
                FTA.Transition "succ" ["N"] noConstraint])]
    restored <- either (fail . explainDecodeError) pure $ decodeGraph $ encodeGraph graph
    print (restored == graph)
```

Add `cfta` and `cfta-serialization` to the caller's dependencies. Add
`cfta-generator` for size queries. For file IO, add `bytestring` and use its
lazy byte strings. The library exposes pure codecs; the application controls
IO errors, file replacement, and input-size limits.

For an interned automaton, first use `Interned.toFTA`. Give its states portable
file-local names with `FTA.mapStates` before encoding. Keep that explicit graph
for subsequent queries. Importing it through interned nodes again can change
ranks by normalizing its structure. Do not store a live `NodeId` as a runtime
reference. A typed Haskell decoder also needs a compatible constructor schema;
a graph snapshot alone does not reconstruct host values or functions.

## Version 1 schema

This is a complete empty language:

```json
{
  "format": "cfta-graph",
  "version": 1,
  "initial": "Empty",
  "states": [{"state": "Empty", "transitions": []}]
}
```

A transition has exactly these fields:

```json
{
  "symbol": {"text": "zero", "refinement": ["top"]},
  "children": [],
  "constraint": {"equalities": [], "guard": ["top"]}
}
```

Object field order is not significant. Arrays retain order. A state value can
be any JSON value supported by its caller-supplied codec; use string names for
cross-language interchange. A symbol's text and refinement together identify
it. Equal text with different refinements can identify different symbols.

A path is an array of machine-sized integer child indexes. An equality class
is an array of paths. `equalities` is an array of classes, or `null` for
`EqContradiction`. For example, `[[[0],[1]]]` requires equal first and second
children. `[]` imposes no equality. The codec preserves compiled classes and
does not merge them. It retains invalid paths already present in an input
graph; the query's constraint interpreter decides their meaning.

Every tagged array has exactly the operands below. Names are JSON strings.
Lists of operands are JSON arrays. `F` denotes a formula, `T` a formula term,
`S` a sort, `G` a guard, and `P` a path.

| Data | Encodings |
| --- | --- |
| Formula | `["top"]`, `["bottom"]`, `["and",[F,...]]`, `["or",[F,...]]`, `["not",F]`, `["atom",relation,T,T]`, `["forall",[[name,S],...],F]`, `["exists",[[name,S],...],F]` |
| Relation | `"eq"`, `"ne"`, `"gt"`, `"ge"`, `"lt"`, `"le"` |
| Formula term | `["integer",decimalString]`, `["variable",name]`, `["application",name,[T,...]]`, `["negate",T]`, `["add",T,T]`, `["subtract",T,T]`, `["multiply",T,T]`, `["divide",T,T]`, `["modulo",T,T]`, `["if",F,T,T]`, `["cast",T,S]` |
| Sort | `["integer"]`, `["real"]`, `["boolean"]`, `["function",[S,...],S]` |
| Guard | `["top"]`, `["bottom"]`, `["same",P,P]`, `["entails",P,P]`, `["satisfies",P,F]`, `["holds",[P,...],F]`, `["substitute",[[actualPath,formalPath],...],G]`, `["not",G]`, `["and",[G,...]]`, `["or",[G,...]]` |

Integer literals use canonical decimal strings, such as `"0"`, `"-42"`, or an
arbitrarily long integer. Leading zeros, a leading plus, fractions, exponents,
and `"-0"` are rejected. This avoids precision loss in JSON consumers with
floating-point numbers. Formula structure is preserved, including empty
connectives, quantifiers, casts, and substitutions. The codec does not claim
that every query backend supports every stored formula.

Duplicate JSON object keys and duplicate decoded state identities are errors.
Missing fields, unknown fields, unknown tags, incorrect operand counts,
unsupported format versions, and trailing data are errors too. The reader
then calls `mkFTA` to check the initial state, child references, and ranked
arities. `explainDecodeError` gives a readable message; callers can inspect
`DecodeError` for structured handling. A document error carries its JSON path,
not a source line number.

Graph snapshots do not retain individual facts that constraint compilation
has combined. Use an editable source document when you need to remove one of
those facts. A query checkpoint additionally needs the graph version, query
route, order, bounds, assumptions, and next position. Those are separate APIs.

## Editable documents

Use `Data.CFTA.Document` when each fact must remain removable. A source graph
has `Annotation name facts` on each transition. The transition name is unique
within its state. `facts` is a `Map Text Constraint`. `mkDocument` checks the
state rows, references, symbol arities, and transition names. `sourceGraph`
exposes these annotations; `compileGraph` combines the remaining facts for
queries. It retains false productions in source. A single fact keeps its exact
syntax when compiled.

`FTA.terms` lists ordinary tree shapes and does not interpret constraints.
Use `Sized.sized` for equality size classes or `Sized.sizedUpTo` with an
entailment solver for semantic guards. The executable uses `sizedUpTo`.

`fromGraph` imports each existing constraint as one fact named `imported`.
It names transitions `t0`, `t1`, and so on within each row. This cannot recover
source facts or alternatives removed before the import. Removing `imported`
removes the complete combined constraint.

`patch before edits` prepares a patch against one source snapshot.
`applyPatch prepared current` checks that `current` equals that snapshot before
applying the ordered edits. It returns a new checked document. The old document
remains available for undo. Any stale snapshot, missing target, duplicate name,
or invalid final graph is an error. Nothing commits partially.

| Edit | Effect |
| --- | --- |
| `PutRow state transitions` | Add or replace a complete row. Preserve the written alternative order. |
| `DeleteRow state` | Remove an existing row. The final graph must still have its initial state and all referenced children. |
| `PutTransition state transition` | Replace the complete named production in place, or append it if the name is new. Use the supplied annotation and facts. |
| `DefineTransition state name symbol children` | Change the constructor and children while retaining existing facts, or append a new production with no facts. |
| `DeleteTransition state transitionName` | Remove one named production. Keep the state row, even when it becomes empty. |
| `SetFact state transitionName factName body` | Add a fact or replace that fact's body. |
| `RemoveFact state transitionName factName` | Remove exactly one existing named fact. |

Named edits require an existing state and a unique production name. They resolve
their target at that point in the edit sequence. Row
edits can introduce forward references if the complete batch supplies the rows.
The initial state stays fixed. There is no implication that an old rank remains
valid after an edit. Rebuild the query for the new graph.

`encodeDocument` and `decodeDocument` store these source definitions as
`cfta-document`, version 1. The graph fields and symbol/refinement codecs are
the same as graph snapshots. Each transition has `symbol`, `children`, `name`,
and `facts`. The `facts` object maps names to the full constraint objects defined
above. For example:

```json
{
  "symbol": {"text": "zero", "refinement": ["top"]},
  "children": [],
  "name": "zero",
  "facts": {"disabled": {"equalities": null, "guard": ["top"]}}
}
```

A document with this transition retains its disabled production. Removing
`disabled` restores it. Duplicate fact keys are errors. Graph and document
readers reject each other's format tag. `InvalidDefinition` reports a document
invariant failure. `explainDecodeError` also renders this error.

Run the complete source-editing example in separate processes:

```sh
cabal run cfta-editable-document -- save /tmp/source.json
cabal run cfta-editable-document -- show /tmp/source.json
cabal run cfta-editable-document -- edit /tmp/source.json /tmp/edited.json
cabal run cfta-editable-document -- show /tmp/edited.json
```

The source language has zero accepted pairs because its `disabled` fact is
false. The patch removes `disabled` and `positive`, retains `same`, and adds the
constructor `two`. The edited language has exactly `pair(zero,zero)`,
`pair(one,one)`, and `pair(two,two)`. Reopening the edited file retains the
remaining fact and constructor names.

The patch keeps a complete starting document and compares its contents. It is
not a compact change log or a constant-time version check. Applying it validates
and rebuilds the graph. Count-table reuse and efficient document digests remain
separate work. Documents store source data; query plans, cursors, host functions,
and serialized patches are not part of this format.

## Compose updates to a language value

Use `Data.CFTA.Language` for the user-facing update expression. Start with
`fromDocument source`, combine changes with `<>`, and call `update` once:

```haskell
modified <- either (fail . Language.explainUpdateError) pure $
    Language.update before $
        Language.define twoRef twoSymbol []
            <> Language.relax pairRef positive
            <> Language.without zeroPairRule (Language.wholeTerm zeroPair)
```

Here `before` is a `Language State`, with an ADT for `State`. `twoRef` and
`pairRef` are `ProductionRef State` values. `positive` is a `FactName`, and
`zeroPairRule` is an `ExclusionName`. `twoSymbol` is the complete constructor
symbol, and `zeroPair` is a term with complete symbols. Declare identifiers once
and reuse these typed bindings. Production, fact, and exclusion names have
distinct types; raw text is used at declaration and codec boundaries. See
[LanguageExpressions.hs](examples/LanguageExpressions.hs) for the complete
program, including the source definition and refined symbols.

| Expression | Effect |
| --- | --- |
| `define (at state name) symbol children` | Change the constructor and children while retaining its facts, or append a new production with no facts. |
| `remove (at state name)` | Remove that production. Other derivations of a term can remain. |
| `require (at state name) fact constraint` | Add or replace one named fact. |
| `relax (at state name) fact` | Remove one existing fact, without negating it. |
| `without name (wholeTerm term)` | Exclude exactly that complete term at the root. |
| `without name (subterm term)` | Exclude terms that contain that subtree. |
| `without name (AtRoot template)` | Exclude complete terms that match a template. |
| `without name (Anywhere template)` | Exclude terms with a matching subtree. |
| `restore name` | Remove that named exclusion. Other exclusions and facts still apply. |
| `editSource edit` | Include a checked source edit, such as a state-row change. |

`define` retains an existing production's facts. Compose `require` or `relax`
to change its obligations explicitly. A new production starts with no facts.
The low-level `editSource (PutTransition ...)` operation remains available when
a complete source replacement, including its facts, is intended. State references
and constructor arities are checked after the complete source batch. Missing
fact, production, state, or exclusion targets report an error.

Templates compare complete symbols, including refinements. A displayed term
with its refinements removed is not the same selector. Retain the original term
when the user selects a result. Use `wholeTerm` for a single complete term and
`subterm` when its occurrences inside larger terms must also be removed.

`Language.source` and `Language.exclusions` retain the editable values. The
compiler applies exclusions to a separate graph. `restore` therefore works
without reconstructing transitions that an exclusion removed or split.
Compiled state numbers are query identities, not editable source names.
Use a constraint-aware query route such as `Sized.sizedUpTo` with a solver.
An update invalidates existing query indexes and rank cursors.

`Update` is a reusable value with inspectable first-order `Operation` values.
It does not record an expected source version. A `Document.Patch` does record
that expected version. The expression API is suitable for local composition;
a remote edit protocol still needs an explicit version check.

Use `encodeLanguage` and `decodeLanguage` to save and reopen the resulting
value. Format `cfta-language`, version 1, contains the complete `cfta-document`
source and a map of named exclusions. Root exclusions use
`["root", template]`; subtree exclusions use `["anywhere", template]`.
Templates use `hole`, `any-node`, `node`, `any-prefix`, or `prefix` tags.
A `node` or `prefix` stores the full symbol and ordered child templates.
Unknown tags, operands, fields, versions, and duplicate keys are errors.

Run the complete expression example without a file:

```sh
cabal run cfta-language-expressions
```

The three size-three/size-four count pairs are `[2,3]`, `[2,2]`, and `[3,3]`.
They show whole-term exclusion, subtree exclusion, and restoration. The `same`
equality fact remains active throughout. The example first restores a disabled
production and adds the refined constructor `two` through one expression.

Persistence uses the same value. Run each command in a separate process:

```sh
cabal run cfta-language-expressions -- save /tmp/language.json
cabal run cfta-language-expressions -- show /tmp/language.json
cabal run cfta-language-expressions -- restore /tmp/language.json /tmp/restored.json
cabal run cfta-language-expressions -- show /tmp/restored.json
```

The saved language gives `[2,3]`. Removing its named exclusion gives `[3,3]`.
The program changes the loaded value through `restore`; it does not edit JSON.
Storage does not include query indexes, cursor state, or update requests.

## Readable definitions with exact round trips

`Data.CFTA.Serialization.Text.printLanguage` prints the complete editable
language. `parseLanguage` reads that form and returns the same value. Use an
expected state type, such as `Language State`, when parsing. The same state
codec and source validation apply to JSON and readable text.

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

This is a stored language value. The constructor, fact, and exclusion names
remain available for typed updates. Parsing does not run a solver, prune the
graph, combine facts, or normalize formulas. State rows with no productions
and rows that the root cannot reach remain present.

The law is `parseLanguage (printLanguage value) == Right value`. Printed text
is canonical. Reprinting a parsed canonical form gives the same text. The parser
also accepts whitespace and `//` line comments; these are not part of the stored
language value and are not preserved by printing.

Names use ASCII identifiers or JSON-quoted strings. The printer quotes unusual
names, `_`, and `json`. Non-string state values use `json(VALUE)`, so ADTs,
records, numbers, arrays, booleans, and null values keep their caller-supplied
state codec. That codec must preserve equality and ordering on a round trip.

A symbol refinement follows `@{ ... }`. Simple comparisons use `v == 0`,
`v /= 0`, `v > 0`, `v >= 0`, `v < 0`, or `v <= 0`. `v` denotes the library's
refinement value. Integers are exact and can exceed machine integer ranges.
`true` and `false` are also formulas. Other formula syntax uses `raw JSON`,
with the complete formula schema above. The printer does not simplify an
`And []`, change `Neg (Lit 1)` to `Lit (-1)`, or discard any other source syntax.

Facts use `true`, `false`, `impossible`, `equal(PATH, ...)`, or
`satisfies(PATH, FORMULA)` when those forms preserve the exact constraint.
For example, `positive = satisfies([0], v > 0);` constrains the first child.
`impossible` keeps an equality contradiction distinct from a false guard.
`equal` stores exactly one equality class, including an empty or singleton
class. All other constraints use `raw JSON` with both equality and guard fields.

Exclusions use `root` or `anywhere`. A template uses `_` for a hole,
`f(a, b)` for an exact node, and `_(a, b)` for any root with those exact children.
A final `...` gives a prefix, such as `f(a, ...)` or `_(...)`. Quote the symbol
`"_"` to distinguish it from a hole. Refinements remain part of symbol matching.

Syntax failures report a line, column, and expected form. Schema and source
failures report their existing JSON path or source identity. Duplicate facts,
exclusions, states, and production names are errors. Unknown versions and
trailing data are errors.

The complete typed example uses the same update API after loading either format:

```sh
cabal run cfta-language-expressions -- print
cabal run cfta-language-expressions -- save-text /tmp/language.cfta
cabal run cfta-language-expressions -- show-text /tmp/language.cfta
cabal run cfta-language-expressions -- restore-text /tmp/language.cfta /tmp/restored.cfta
cabal run cfta-language-expressions -- show-text /tmp/restored.cfta
```

The stored language gives counts `[2,3]` at sizes three and four. Removing the
named exclusion gives `[3,3]`, exactly as for JSON. File and standard-output
encoding is UTF-8. No manual file edit is needed. A quasiquoter can reuse this
pure parser; this package does not add a separate quote semantics.

See the [language authoring comparison](../docs/language-authoring-prior-art.md)
for Redex and data-format prior art, implementation limits, and planned
pattern bindings and portable update expressions.
