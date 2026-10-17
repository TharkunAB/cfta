# cfta-serialization

Read and write complete FTA, ECTA, and LTA graphs and editable language values.
`Data.CFTA.Serialization.Text` provides one readable format. It retains full
refinements, every constraint constructor, individual source facts, named
exclusions, cycles, empty/dead rows, repeated alternatives, and child order.
Reading validates the source without running a solver or enumerating terms.

The format is version 2. It replaces the earlier JSON and readable-v1 prototypes;
those decoders are removed. No JSON syntax or Aeson instance is required.

## Typed values and exact round trips

| Value | Printer | Parser | Header |
| --- | --- | --- | --- |
| `PlainFTA state Symbol` | `printGraph` | `parseGraph` | `graph 2;` |
| `Document state` | `printDocument` | `parseDocument` | `document 2;` |
| `Language state` | `printLanguage` | `parseLanguage` | `language 2;` |

Printers return `Text`. Parsers return `Either (TextError state) value`.
`explainTextError` reports a syntax line/column or a checked source error.
The default state labels use `Show` and `Read`. For lawful instances:

```haskell
parseLanguage (printLanguage language) == Right language
```

Printing a parsed canonical form reproduces that form. Input spacing and `//`
line comments are presentation and are not retained. No constraint normalization
occurs during reading or writing. Empty connectives and stored equality classes
remain distinct even when they have the same meaning.

Use an ADT for source states. For example:

```haskell
data State = Atom | Expr deriving (Eq, Ord, Show, Read)
```

For custom or portable state labels, use `StateCodec state` and the corresponding
`printGraphWith`/`parseGraphWith`, `printDocumentWith`/`parseDocumentWith`, or
`printLanguageWith`/`parseLanguageWith` functions. The codec contains
`encodeState :: state -> Text` and `decodeState :: Text -> Either String state`.
The snapshot printer handles quoting. For a graph with `Text` state names:

```haskell
textStates = StateCodec id Right
```

Decoding an encoded state must return that exact state and preserve equality and
ordering. A structured state such as `Index 3` can use derived `Show`/`Read`; its
label is printed as `"Index 3"`. State labels are the only caller-defined codec.
Constraints, symbols, paths, and source operations remain typed values.

## A complete readable language

```text
language 2;
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

A source production has a stable name, complete symbol, ordered child states,
and optional named facts. Only an exact top symbol refinement is omitted.
Production names are unique within their state. Fact and exclusion names must
also be unique in their scope. Unknown references and inconsistent symbol arities
are errors. Duplicate source states are errors even when their rows are identical.

A document uses the same source rows with a `document 2;` header. A graph stores
compiled constraints directly, without introducing source fact identities:

```text
graph 2;
start Expr;
state Atom {
  zero @{ v == 0 };
  one @{ v == 1 };
}
state Expr {
  pair(Atom, Atom) where constraint([[[0], [1]]], satisfies([0], v > 0));
  wrap(Expr);
}
```

Names can use ASCII letters, digits, `_`, `-`, and `+`. Other names use double
quotes. Quoted strings retain Unicode and escaped control characters. Supported
escapes are `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t`, and `\uXXXX`;
a non-BMP escape uses a valid surrogate pair. The printer quotes the name `_`
to distinguish it from a template hole.

## Complete constraint syntax

A path is a list of zero-based child indexes, such as `[0, 1]`. The format also
retains invalid stored paths because they are part of the source value. An index
outside the machine `Int` range is rejected instead of overflowing.

| Constraint | Exact stored value |
| --- | --- |
| `true` or `false` | No equality classes, with a top or bottom guard |
| `equal([0], [1])` | One equality class and a top guard |
| `equal()` | One empty equality class and a top guard |
| `impossible` | Equality contradiction and a top guard |
| Any guard form below | No equality classes, with that guard |
| `constraint(CLASSES, GUARD)` | Both fields explicitly |

`CLASSES` is `impossible` or a list of path classes, such as
`[[[0], [1]], [[1], [2]]]`. Class order and empty/singleton classes are retained.
Paths within one class are a set. Removing a source fact removes that obligation;
it does not negate the constraint or reconstruct facts lost during compilation.

| Guard | Operands |
| --- | --- |
| `same(P, Q)` | Equal annotated subterms at two paths |
| `entails(P, Q)` | Refinement implication between paths |
| `satisfies(P, F)` | A formula required at a path |
| `holds([P, ...], F)` | A formula over the selected paths |
| `substitute([(ACTUAL, FORMAL), ...], G)` | Ordered actual-for-formal substitutions |
| `not(G)`, `and(G, ...)`, `or(G, ...)` | Exact Boolean constructors |
| `true`, `false` | Top and bottom |

Formulas use `true`, `false`, `and(F, ...)`, `or(F, ...)`, and `not(F)`.
Comparisons are `eq(A, B)`, `ne`, `gt`, `ge`, `lt`, and `le`. A comparison of the
distinguished refinement value with an integer has the concise form `v == 0`,
with `==`, `/=`, `>`, `>=`, `<`, or `<=`. Quantifiers retain ordered bindings:

```text
forall([x: int, f: function([int], bool)], ge(var(x), 0))
exists([x: int], and(gt(var(x), 0), lt(var(x), 10)))
```

Formula terms are exact signed integers, `v`, `var(NAME)`, `app(NAME, [TERM, ...])`,
`negate(T)`, `add(A, B)`, `subtract(A, B)`, `multiply(A, B)`, `divide(A, B)`,
`modulo(A, B)`, `if(F, A, B)`, and `cast(T, SORT)`. Integers have no precision
limit. `negate(1)` remains distinct from `-1`. `var(v)` is an ordinary variable
named `v`, distinct from the distinguished value abbreviated as `v`.
Sorts are `int`, `real`, `bool`, and `function([SORT, ...], RESULT)`.

These are representations of existing typed constructors. A query backend still
needs to support the stored constraints. Exact storage does not establish that
an arbitrary formula can be decided or enumerated.

## Natural updates and reversible exclusions

Modify the typed language value, then save it:

```haskell
modified <- either (fail . Language.explainUpdateError) pure $
    Language.update before $
        Language.define twoRef twoSymbol []
            <> Language.relax pairRef positive
            <> Language.without zeroPairRule (Language.wholeTerm zeroPair)
```

`twoRef` and `pairRef` are `ProductionRef State` values. `positive` is a
`FactName`; `zeroPairRule` is an `ExclusionName`. Declare identifiers once and
reuse typed references. See [LanguageExpressions.hs](examples/LanguageExpressions.hs)
for the complete program, including its ADT states, definitions, and refinements.

| Expression | Effect |
| --- | --- |
| `define reference symbol children` | Change an existing production while retaining its facts, or append a new production with no facts |
| `remove reference` | Remove that production |
| `require reference fact constraint` | Add or replace one named fact |
| `relax reference fact` | Remove an existing fact |
| `without name (wholeTerm term)` | Exclude exactly that complete root term |
| `without name (subterm term)` | Exclude terms that contain that subtree |
| `without name (AtRoot template)` or `Anywhere template` | Exclude a root or subtree pattern |
| `restore name` | Remove only that named exclusion |
| `editSource edit` | Include a checked source edit, such as a state-row change |

The source definition remains available when exclusions split or remove compiled
transitions. `define` retains existing facts; adjust constraints explicitly with
`require` or `relax`. Whole-term addition must not bypass constraints. It remains
a separate pending operation.

Templates use `_` for a hole, `f(a, b)` for an exact node, `_(a, b)` for any
symbol with those children, and a final `...` for a prefix. Thus `f(...)` and
`_(...)` differ from exact leaves. Templates retain complete symbol refinements.
A displayed term after `eraseRefinements` is not a complete edit selector.

`Document.Patch` stores an expected source document and rejects a stale edit.
`Language.Update` is a reusable expression without that version check. The
low-level `PutTransition` replaces a complete production and its facts;
`DefineTransition` retains existing facts. Source edits validate the final batch.

## Save, reopen, inspect, and modify

Run these complete examples in separate processes:

```sh
cabal run cfta-graph-snapshot -- save /tmp/graph.cfta
cabal run cfta-graph-snapshot -- load /tmp/graph.cfta

cabal run cfta-editable-document -- save /tmp/source.cfta
cabal run cfta-editable-document -- edit /tmp/source.cfta /tmp/edited.cfta
cabal run cfta-editable-document -- show /tmp/edited.cfta

cabal run cfta-language-expressions -- print
cabal run cfta-language-expressions -- save /tmp/language.cfta
cabal run cfta-language-expressions -- show /tmp/language.cfta
cabal run cfta-language-expressions -- restore /tmp/language.cfta /tmp/restored.cfta
cabal run cfta-language-expressions -- show /tmp/restored.cfta
```

The examples use explicit UTF-8 and atomic file replacement. The graph returns
counts `[0,0,1,1,1]`. The source edit removes `disabled` and `positive`, keeps
`same`, and adds `two`, producing three equal pairs. The language example shows
counts `[2,3]` for root exclusion, `[2,2]` for subtree exclusion, and `[3,3]` after
restoration. Editing a file is not required for any update.

Use a constraint-aware query route such as `Sized.sizedUpTo` with a solver.
`FTA.terms` ignores constraints, and `FTA.accepts` is not a general guard solver.
A saved value does not contain a query cursor, count tables, solver state, or host
functions. Rebuild the same query route and ordering policy to retain ranks;
an edit invalidates old indexes and cursors. Query checkpoints remain pending.

The [prior-art comparison](../docs/language-authoring-prior-art.md) covers Liquid
Haskell, Redex, Nanopass, Turnstile, and data notations. Named pattern bindings,
serialized updates, a shared runtime/quasiquote interface, and the typed-language
and Lean spike remain pending. The complete logical syntax here preserves values;
it does not claim a complete dependent type system.
