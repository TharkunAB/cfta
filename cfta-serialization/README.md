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
