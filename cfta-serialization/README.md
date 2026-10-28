# cfta-serialization

Read and write complete FTA, ECTA, and LTA graphs, editable language values,
and query checkpoints.
`Data.CFTA.Serialization.Text` provides one readable format. It retains full
refinements, every constraint constructor, individual source facts, named
exclusions, cycles, empty/dead rows, repeated alternatives, and child order.
Reading validates the input without running a solver or enumerating terms.

The format is version 1. Each file starts with its kind and version, such as
`graph 1;` or `language 1;`. The [grammar](#grammar) gives the complete syntax,
and [versions](#versions) says when a version changes.
[Prior art](../docs/language-authoring-prior-art.md) compares this syntax with
Redex, Nanopass, EDN, and KDL, and explains why the format has its own syntax.

## Typed values and exact round trips

| Value | Printer | Parser | Header |
| --- | --- | --- | --- |
| `PlainFTA state Symbol` | `printGraph` | `parseGraph` | `graph 1;` |
| `Document state` | `printDocument` | `parseDocument` | `document 1;` |
| `Language state` | `printLanguage` | `parseLanguage` | `language 1;` |
| `Checkpoint state` | `printCheckpoint` | `parseCheckpoint` | `checkpoint 1;` |
| `SamplingCheckpoint state` | `printSamplingCheckpoint` | `parseSamplingCheckpoint` | `sampling 1;` |

Printers return `Text`. Parsers return `Either (TextError state) value`.
`explainTextError` reports a syntax line/column, a checked graph error, or a
checked source error.
The default state labels use `Show` and `Read`. For lawful instances:

```haskell
parseGraph (printGraph graph) == Right graph
```

Printing a parsed canonical form reproduces that form. Input spacing and `//`
line comments are presentation and are not retained. Doc comments (`///`) and
the sorts of states are kept beside the value: see [Doc comments](#doc-comments)
and [Sorts](#sorts). No constraint normalization occurs during reading or
writing. Empty connectives and stored equality classes remain distinct even when
they have the same meaning.

Use an ADT for states. For example:

```haskell
data State = Atom | Expr deriving (Eq, Ord, Show, Read)
```

For custom or portable state labels, use `StateCodec state` and the corresponding
`printGraphWith`/`parseGraphWith`, `printDocumentWith`/`parseDocumentWith`,
`printLanguageWith`/`parseLanguageWith`,
`printCheckpointWith`/`parseCheckpointWith`, or
`printSamplingCheckpointWith`/`parseSamplingCheckpointWith` functions. The codec contains
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

## Doc comments

A line that starts with exactly three slashes, `///`, is a doc comment. It
documents the item after it: the header of the file, a state, a production, a
fact, or an exclusion. A graph transition has no doc comment. A `//` comment,
and a comment with four or more slashes, is not kept.

```text
/// Pairs of small numbers.
language 1;
start Expr;

/// The leaves.
state Atom {
  zero = zero @{ v == 0 };
  one = one @{ v == 1 };
}

state Expr {
  /// A pair of atoms.
  pair = pair(Atom, Atom) {
    /// Both atoms are the same.
    same = equal([0], [1]);
  };
}

/// A pair of zeros is not a term.
exclude zero-pair = root pair(zero @{ v == 0 }, zero @{ v == 0 });
```

The doc comments are kept beside the value, in `Notes state`. Its field
`noteComments` maps a `CommentTarget state` (`OnFile`, `OnState`,
`OnProduction`, `OnFact`, or `OnExclusion`) to the text of the comment. One
space after `///` is not part of the text. Consecutive comment lines are one
text, with a newline between the lines.

| Value | Printer | Parser |
| --- | --- | --- |
| `PlainFTA state Symbol` | `printGraphNotesWith` | `parseGraphNotesWith` |
| `Document state` | `printDocumentNotesWith` | `parseDocumentNotesWith` |
| `Language state` | `printLanguageNotesWith` | `parseLanguageNotesWith` |

Each takes a `StateCodec`. `showCodec` gives the state labels of `printGraph`
and `parseGraph`. The other readers read doc comments and drop them. A doc
comment that does not come before one of these items is a syntax error. The
printer prints no comment for an item that the value does not have.

`mempty` is no notes, and `printGraphNotesWith codec mempty` prints the text of
`printGraphWith codec`. A doc comment is not part of the value. It does not
change the equality of the value, the text of `printGraph`, or a checkpoint, so
a new comment does not make a checkpoint stale.

## Sorts

A state of a graph, a document, or a language can have a sort, written after
its name: `state Pos : Int {`. The sorts are kept beside the value, in the field
`noteSorts` of `Notes`, as the doc comments are. The printers and parsers with
notes keep them; the other readers drop them.

```text
graph 1;
start Test;

state Small : Int {
  zero @{ v == 0 };
  one;
}

state Sum : Int {
  add(Sum, Small);
  zero;
}

state Test : Bool {
  lt(Sum, Small);
}
```

A state is a refinement of its sort: here `Small` and `Sum` are two sets of
terms of sort `Int`. `checkSorts` of `Data.CFTA.Gen.ManySorted` in
`cfta-generator` checks the sorts against a signature: each transition
`f(q1, ..., qn)` of a state `q` must be a function `f` from the sorts of
`q1, ..., qn` to the sort of `q`. For refined symbols, check the graph after
`FTA.mapSymbols unrefined`.

## Signatures

`printSignature` and `parseSignature` store a `SortedSignature` of
`Data.CFTA.Signature`: the sorts, the root sorts, the sorts with values, and the
functions with their argument and result sorts. `printSignatureWith` and
`parseSignatureWith` take a `StateCodec` for the sorts and one for the symbols.

```text
signature 1;

sort Int;
sort Bool;
root Bool;
values Int = interval(-10, 10);
function zero : Int;
function one : Int;
function add : (Int, Int) -> Int;
function lt : (Int, Int) -> Bool;
```

Each element of each list is one statement, in the order of its list, so a
parsed signature is equal to the printed one. A constant has no argument list.
`values NAME = pool(SYMBOL, ...)` gives a sort the values of a pool. Reading
checks the syntax only; `checkSignatureWith` of `Data.CFTA.Gen.ManySorted`
checks the signature. A signature file has no doc comments.

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
A named predicate is `predicate(NAME, [TERM, ...])`. The empty argument list
is kept, so `predicate(ready, [])` is a predicate with no arguments.
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
Sorts are `int`, `real`, `bool`, `function([SORT, ...], RESULT)`, and
`named(NAME, [SORT, ...])`. For example, `named(List, [int])` is a named type
constructor with its arguments. The format stores the names of predicates and
sorts; it does not store their definitions.

These are representations of existing typed constructors. A query backend still
needs to support the stored constraints. Exact storage does not establish that
an arbitrary formula can be decided or enumerated.

## Exclusion templates

A language stores its named exclusions as `exclude NAME = root TEMPLATE;` or
`exclude NAME = anywhere TEMPLATE;`. Templates use `_` for a hole, `f(a, b)` for
an exact node, `_(a, b)` for any symbol with those children, and a final `...`
for a prefix. `_x` is a named hole: it matches any subterm, as `_` does, and
gives it the name `x`. No space comes between `_` and the name. A template
quotes a symbol whose name starts with `_`, such as `"_f"(a)`. Thus `f(...)` and `_(...)` differ from exact leaves. Templates keep
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
start Expr;
```

`define`, `remove`, `require`, `relax`, and `start` are the operations of the
same names in `Data.CFTA.Language`. `put production`, `put row`, and
`delete row` are the source edits `PutTransition`, `PutRow`, and `DeleteRow`.
`start` is the source edit `SetStart`, written as the `start` line of a
document. An update does not name the language it changes: apply it with
`Language.update`, which checks it.

## Checkpoints

`printCheckpoint` and `parseCheckpoint` store a `Checkpoint` of
`Data.CFTA.Checkpoint`: a saved position in a size-ordered listing of the
terms of a graph. `Data.CFTA.Sized.Checkpoint` of
[cfta-generator](../cfta-generator/README.md) makes and resumes it.

```text
checkpoint 1;
query sized 1;
bound 7;
next 5 1;

graph 1;
start tree;

state tree {
  leaf;
  node(tree, tree);
}
```

`query` gives the route and its version. The route and its version fix the
order of the listing. `bound` gives the largest size in the listing. `next`
gives the sized rank of the next term: its size, then its class rank. The
remaining text is the text of `printGraph` for the graph. Thus the checkpoint
holds its graph, and the printed graph is the identity of the checkpoint. No
hash is necessary, and one file is sufficient to resume.

To resume in a new process, read the checkpoint and the current graph. Here
the states are text, as with `textStates` above:

```haskell
saved <- either (fail . T.explainTextError) pure $ T.parseCheckpointWith textStates checkpointText
graph <- either (fail . T.explainTextError) pure $ T.parseGraphWith textStates graphText
rest <- either (fail . show) pure $ Checkpoint.resume saved graph
```

`resume` builds the size classes of the graph again. It rejects a graph that
is not equal to the graph of the checkpoint, and names the first row that
differs. A new order of the transitions of one state also makes a checkpoint
stale, because the ranks follow the order of the rows. To resume the saved
version, use `checkpointGraph saved` as the graph. To continue in an edited
graph, use `relocate`: it does not continue the old listing.

## Sampling checkpoints

`printSamplingCheckpoint` and `parseSamplingCheckpoint` store a
`SamplingCheckpoint`: a saved position in a sampled run of draws from the
same listing. `startSampling` and `resumeSampling` of
`Data.CFTA.Sized.Checkpoint` make and resume it.

```text
sampling 1;
query sized-sample 1;
bound 7;
weights [1: 1, 5: 3];
prng splitmix64 1;
seed 11;
draws 12;

graph 1;
start tree;

state tree {
  leaf;
  node(tree, tree);
}
```

`weights` gives a weight for each size, as `SIZE: WEIGHT`, or `uniform` for
the same chance for each term of the listing. `prng` gives the pseudorandom
generator and its version. `seed` is a 64-bit word, and `draws` is the number
of draws before the next draw. A draw depends only on the seed and on its
index, so the file holds no state of the generator. As in a checkpoint, the
remaining text is the text of `printGraph` for the graph. `resumeSampling`
rejects another graph and other weights.

## Grammar

The grammar uses EBNF: `?` is optional, `*` is zero or more, and `+` is one or
more. Spaces, line breaks, and `//` comments can come between any two tokens.
A `name` is a state label, the sort of a state, a symbol, or a name of a
production, a fact, an exclusion, or a variable. The printer leaves a name
unquoted when every character is an ASCII letter, a digit, `_`, `-`, or `+`,
and the name is not `_`. It quotes every other name.

```ebnf
graph-file      = header("graph") graph-row* ;
document-file   = header("document") source-row* ;
language-file   = header("language") source-row* exclusion* ;
header(kind)    = doc-comment? kind "1" ";" "start" name ";" ;

graph-row       = doc-comment? "state" name ( ":" name )? "{" graph-edge* "}" ";"? ;
graph-edge      = symbol children? ( "where" constraint )? ";" ;
source-row      = doc-comment? "state" name ( ":" name )? "{" production* "}" ";"? ;
production      = doc-comment? name "=" symbol children? ( "{" fact* "}" )? ";" ;
fact            = doc-comment? name "=" constraint ";" ;
exclusion       = doc-comment? "exclude" exclusion-body ;
exclusion-body  = name "=" ( "root" | "anywhere" ) template ";" ;
symbol          = name ( "@" "{" formula "}" )? ;
children        = "(" ( name ( "," name )* )? ")" ;

signature-file  = "signature" "1" ";" signature-statement* ;
signature-statement
                = ( "sort" | "root" ) name ";"
                | "values" name "=" ( "interval" "(" integer "," integer ")"
                                    | "pool" "(" ( name ( "," name )* )? ")" ) ";"
                | "function" name ":" ( "(" ( name ( "," name )* )? ")" "->" )? name ";" ;

update-file     = "update" "1" ";" operation* ;
operation       = "start" name ";"
                | "define" name name "=" symbol children? ";"
                | "remove" name name ";"
                | "require" name name name "=" constraint ";"
                | "relax" name name name ";"
                | "put" "production" name production
                | "put" "row" name "{" production* "}"
                | "delete" "row" name ";"
                | "exclude" exclusion-body
                | "restore" name ";" ;

checkpoint-file = "checkpoint" "1" ";" query "next" integer integer ";" graph-file ;
sampling-file   = "sampling" "1" ";" query
                  "weights" ( "uniform" | "[" ( weight ( "," weight )* )? "]" ) ";"
                  "prng" name integer ";" "seed" integer ";" "draws" integer ";" graph-file ;
query           = "query" name integer ";" "bound" integer ";" ;
weight          = integer ":" integer ;

constraint      = "equal" "(" ( path ( "," path )* )? ")"
                | "impossible"
                | "constraint" "(" classes "," guard ")"
                | guard ;
classes         = "impossible" | "[" ( paths ( "," paths )* )? "]" ;
paths           = "[" ( path ( "," path )* )? "]" ;
path            = "[" ( integer ( "," integer )* )? "]" ;
guard           = "true" | "false"
                | ( "same" | "entails" ) "(" path "," path ")"
                | "satisfies" "(" path "," formula ")"
                | "holds" "(" paths "," formula ")"
                | "substitute" "(" "[" ( substitution ( "," substitution )* )? "]" "," guard ")"
                | "not" "(" guard ")"
                | ( "and" | "or" ) "(" ( guard ( "," guard )* )? ")" ;
substitution    = "(" path "," path ")" ;

formula         = "true" | "false"
                | ( "and" | "or" ) "(" ( formula ( "," formula )* )? ")"
                | "not" "(" formula ")"
                | "v" ( "==" | "/=" | ">=" | "<=" | ">" | "<" ) integer
                | ( "eq" | "ne" | "gt" | "ge" | "lt" | "le" ) "(" term "," term ")"
                | ( "forall" | "exists" ) "(" "[" ( binding ( "," binding )* )? "]" "," formula ")"
                | "predicate" "(" name "," "[" ( term ( "," term )* )? "]" ")" ;
binding         = name ":" sort ;
term            = integer | "v" | "var" "(" name ")"
                | "app" "(" name "," "[" ( term ( "," term )* )? "]" ")"
                | "negate" "(" term ")"
                | ( "add" | "subtract" | "multiply" | "divide" | "modulo" ) "(" term "," term ")"
                | "if" "(" formula "," term "," term ")"
                | "cast" "(" term "," sort ")" ;
sort            = "int" | "real" | "bool"
                | "function" "(" "[" ( sort ( "," sort )* )? "]" "," sort ")"
                | "named" "(" name "," "[" ( sort ( "," sort )* )? "]" ")" ;

template        = "_" name | ( "_" | symbol ) template-args? ;
template-args   = "(" ( "..." | template ( "," template )* ( "," "..." )? )? ")" ;

name            = name-char+ | '"' ( string-char | escape )* '"' ;
name-char       = ASCII letter | digit | "_" | "-" | "+" ;
escape          = "\" ( '"' | "\" | "/" | "b" | "f" | "n" | "r" | "t" | "u" hex hex hex hex ) ;
integer         = ( "+" | "-" )? digit+ ;
doc-comment     = ( "///" any character except a line break, to the end of the line )+ ;
```

A `string-char` is any character except `"`, `\`, and a control character
below U+0020. A comment that starts with four or more slashes is an ordinary
comment. The keywords, such as `state` and `true`, are not reserved: a name can
have the same text.

## Versions

Each file starts with its kind and a version, such as `graph 1;` or `signature 1;`. A reader
rejects a version that it does not know. After the first release of
`cfta-serialization`, these rules apply to each kind:

- Printing is stable within a version: a value prints as the same text. A
  program can use the printed text as an identity, so a change to the printed
  text of an existing value needs a new version.
- A change that gives existing text a different value needs a new version.
- An addition that a reader of the version rejects, such as a new constraint
  constructor, keeps the version. A new file can then fail in an older reader,
  but it is not read as a different value.
- An addition that a reader of the version can skip keeps the version. Doc
  comments are such an addition: a reader that does not keep them reads them as
  `//` comments.

Until the first release, version 1 can still change.

## Ranks after reopening

A graph file stores the graph only: no query state, count tables, solver
state, or host functions. A checkpoint file also stores a query and a
position, but no count tables or solver state. Build the same query again
after reading, for example with `Sized.sizedUpTo` and a solver. The reopened graph is equal to the saved graph,
so it gives the same counts, terms, and ranks. An edit can change the ranks.
`FTA.terms` ignores constraints, and `FTA.accepts` does not solve guards.
