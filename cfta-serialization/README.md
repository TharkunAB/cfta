# cfta-serialization

Read and write complete FTA, ECTA, and LTA graphs and editable language values.
`Data.CFTA.Serialization.Text` provides one readable format. It retains full
refinements, every constraint constructor, individual source facts, named
exclusions, cycles, empty/dead rows, repeated alternatives, and child order.
Reading validates the input without running a solver or enumerating terms.

The format is version 1. Each file starts with its kind and version, such as
`graph 1;` or `language 1;`.
[Prior art](../docs/language-authoring-prior-art.md) compares this syntax with
Redex, Nanopass, EDN, and KDL, and explains why the format has its own syntax.

## Typed values and exact round trips

| Value | Printer | Parser | Header |
| --- | --- | --- | --- |
| `PlainFTA state Symbol` | `printGraph` | `parseGraph` | `graph 1;` |
| `Document state` | `printDocument` | `parseDocument` | `document 1;` |
| `Language state` | `printLanguage` | `parseLanguage` | `language 1;` |

Printers return `Text`. Parsers return `Either (TextError state) value`.
`explainTextError` reports a syntax line/column, a checked graph error, or a
checked source error.
The default state labels use `Show` and `Read`. For lawful instances:

```haskell
parseGraph (printGraph graph) == Right graph
```

Printing a parsed canonical form reproduces that form. Input spacing and `//`
line comments are presentation and are not retained. No constraint normalization
occurs during reading or writing. Empty connectives and stored equality classes
remain distinct even when they have the same meaning.

Use an ADT for states. For example:

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

## A complete readable graph

```text
graph 1;
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

A transition has a complete symbol, ordered child states, and an optional
constraint after `where`. Only an exact top symbol refinement is omitted.
Unknown references and inconsistent symbol arities are errors. Duplicate states
are errors even when their rows are identical.

## A complete readable language

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

A source production has a stable name, complete symbol, ordered child states,
and optional named facts. Only an exact top symbol refinement is omitted.
Production names are unique within their state. Fact and exclusion names must
also be unique in their scope. Unknown references and inconsistent symbol arities
are errors. Duplicate source states are errors even when their rows are identical.

A document uses the same source rows with a `document 1;` header.

Names can use ASCII letters, digits, `_`, `-`, and `+`. Other names use double
quotes. Quoted strings retain Unicode and escaped control characters. Supported
escapes are `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t`, and `\uXXXX`;
a non-BMP escape uses a valid surrogate pair. The printer quotes the name `_`
to distinguish it from a template hole.

## Complete constraint syntax

A path is a list of zero-based child indexes, such as `[0, 1]`. The format also
retains invalid stored paths because they are part of the stored value. An index
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

## Exclusion templates

A language stores its named exclusions as `exclude NAME = root TEMPLATE;` or
`exclude NAME = anywhere TEMPLATE;`. Templates use `_` for a hole, `f(a, b)` for
an exact node, `_(a, b)` for any symbol with those children, and a final `...`
for a prefix. Thus `f(...)` and `_(...)` differ from exact leaves. Templates keep
complete symbol refinements, so a term printed after `eraseRefinements` does not
select the same terms. See [editable languages](../docs/editable-languages.md)
for the updates that change a language before you save it.

## Updates

`printUpdate` and `parseUpdate` store a `Language.Update`, so that a list of
changes can be saved and applied again later. Each operation is one statement,
in order, with the same names, symbols, constraints, and templates as a
language:

```text
update 1;
define Atom two = two @{ v == 2 };
require Expr pair same = equal([0], [1]);
relax Expr pair positive;
remove Atom one;
put production Atom three = three {
  never = false;
};
put row Extra {
  leaf = leaf;
}
delete row Extra;
exclude zero-pair = root pair(zero @{ v == 0 }, zero @{ v == 0 });
restore old-rule;
```

`define`, `remove`, `require`, and `relax` are the operations of the same names
in `Data.CFTA.Language`. `put production`, `put row`, and `delete row` are the
source edits `PutTransition`, `PutRow`, and `DeleteRow`. An update does not
name the language it changes: apply it with `Language.update`, which checks it.

## Ranks after reopening

A file stores the graph only: no query state, count tables, solver state, or
host functions. Build the same query again after reading, for example with
`Sized.sizedUpTo` and a solver. The reopened graph is equal to the saved graph,
so it gives the same counts, terms, and ranks. An edit can change the ranks.
`FTA.terms` ignores constraints, and `FTA.accepts` does not solve guards.
