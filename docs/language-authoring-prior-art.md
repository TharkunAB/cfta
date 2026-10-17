# Prior art for language definitions and updates

The target is a complete language value that a person can inspect, a program can
change, and another process can reopen. The definition must retain production
identities and individual facts. Its compiled language must still support exact
synthesis, indexing, and sampling. A notation does not establish these properties.

## Racket and Redex

Redex is the closest prior art for the definition UX. It provides recursive tree
patterns, language extension, and binding declarations. Extension can retain old
alternatives or replace a nonterminal. This makes a language change a separate
expression. See [Redex languages](https://docs.racket-lang.org/redex/Languages.html).

For example, the structural part of the pair language can be written in Redex as:

```racket
(define-language P
  (a ::= zero one)
  (e ::= (pair a_same a_same) (wrap e)))

(define-extended-language P+two P
  (a ::= .... two))
```

This is Redex syntax, not a supported CFTA input. The `....` retains the old
alternatives. Replacing that clause with `(a ::= two)` removes them. The repeated
`a_same` requires identical subterms; repeated plain `a` in a grammar does not.
CFTA can translate such a repeated binding into equality between child paths.
The binding must also have a stable fact identity so that a later update can
remove that fact. See [Redex patterns](https://docs.racket-lang.org/redex/Patterns.html).

Redex judgments provide named inference rules, signatures, and optional input and
output modes. Modes make the permitted direction of computation explicit. A
judgment without a mode can check a supplied derivation. This is useful prior art
for object-language typing and a later proof interchange, but it does not itself
provide a finite tree-automaton translation. See
[Redex judgments](https://docs.racket-lang.org/redex/Other_Relations.html).

There is an important enumeration limit. `redex-enum` cannot construct an
enumerator for side-condition patterns. Two-way enumeration also requires an
unambiguous pattern and has other implementation limits. Random generation can
use rejection for side conditions. Therefore CFTA should accept only constraints
that its selected query backend can handle; it must not promise exact ranks for
arbitrary host predicates. See
[Redex testing and enumeration](https://docs.racket-lang.org/redex/Testing.html).

Racket's `syntax-spec` also separates binding classes, grammar declarations,
extensions, and the host interface. A reference with the wrong binding class is
an error. This supports the use of distinct CFTA production, fact, and exclusion
identities, and suggests typed references in a future quoter. Its macro expansion
is not a portable saved value. See
[syntax-spec](https://docs.racket-lang.org/syntax-spec-v3/Specifying_languages.html).

## Nanopass and Turnstile

Nanopass directly addresses a sequence of related languages. An `extends` clause
selects a base language; `+` and `-` clauses add and remove productions. For a base
with a `wrap` production, an extension can have this form:

```racket
(define-language L1
  (extends L0)
  (Expr (e)
    (- (wrap e))
    (+ (two))))
```

It also generates term parsers and unparsers. `language->s-expression` exposes
the complete extended language. This is close to the desired define, modify,
inspect workflow. Terminal predicates and optional prettifiers can still depend
on host code; the format alone does not supply portable constraints or stable
ranks. See [Nanopass](https://docs.racket-lang.org/nanopass/index.html).

For CFTA, use a complete snapshot for reopening and a typed update expression
for changes. Preserve named facts when adding or removing constructors. A later
portable constructor schema could generate term readers and printers together,
so a displayed term remains a complete selector for an update.

Turnstile combines type checking and macro expansion through declarative rules.
Its bidirectional judgments distinguish synthesizing a type from checking an
expression against a supplied type. This is relevant to a typed language quoter:
show premises and type errors in terms of the declared language. It is not a
portable constraint engine or an enumeration guarantee. See the
[Turnstile guide](https://docs.racket-lang.org/turnstile/The_Turnstile_Guide.html).

## Data notation comparison

These are format properties and proposed mappings, not implemented importers.
Every candidate still needs the CFTA graph, constraint, and identity checks.

| Candidate | Useful property | Requirement for this library |
| --- | --- | --- |
| S-expressions | Constructor applications and nested expressions have one regular shape. | Specify atoms, escaping, numeric precision, versions, and every domain form. Parentheses alone are not a complete interchange specification. |
| EDN | Lists, vectors, maps, keywords, and tagged values can represent typed syntax directly. | Keep alternatives in vectors; map order has no meaning. Validate the domain after reading. Require exact integers and reject duplicate identities. |
| KDL | Named nodes, arguments, properties, and ordered children give compact block notation. | Specify how facts, formulas, state references, and term trees map to nodes. Preserve order where ranks depend on it. |
| JSON5 / Hjson | Comments and less punctuation can improve an existing JSON document. | The verbose graph schema remains. Neither supplies language extension or constraint semantics. |
| Grammar blocks in this PR | Common productions, refinements, facts, and exclusions are concise. | Maintain a small domain parser. Complex constraints still use the full JSON form. |

Sources: [EDN specification](https://github.com/edn-format/edn),
[KDL specification](https://kdl.dev/spec/), [JSON5 specification](https://spec.json5.org/),
and [Hjson syntax](https://hjson.github.io/syntax.html).

The same production and named equality fact have these possible representations.
The EDN and KDL mappings below are illustrations, not additional accepted syntax.

```clojure
;; EDN: production name, symbol, ordered children, named facts
#cfta/production [pair pair [Atom Atom] {same (equal [0] [1])}]
```

```kdl
production pair pair Atom Atom {
  fact same {
    equal {
      path 0
      path 1
    }
  }
}
```

```text
pair = pair(Atom, Atom) {
  same = equal([0], [1]);
};
```

EDN can also express changes as data, for example
`(relax [Expr pair] same)`. That would require a specified interpreter over typed
operations, rather than evaluation as a host program. It would be a useful
meta-language even when the printed snapshot uses grammar blocks.

## Haskell implementation check

The inspected packages are `hedn-0.3.0.5` and `kdl-hs-1.2.1`. Their source archives
are the evidence for these package-specific observations, not a claim about all
EDN or KDL implementations.

`hedn` exposes an AST parser, printer, and quasiquoter. Its AST stores an integer
in `Int` and a decimal in `Double`. Its map constructor uses `Map.fromList`, so
parsing loses duplicate keys before a CFTA decoder can reject them. The string
reader also has an unimplemented Unicode escape case. These are unsuitable
boundaries for exact arbitrary integers, duplicate diagnostics, and complete
text input. A capped probe of the unmodified parser confirms that duplicate
`:same` keys keep only the last value, `9223372036854775808` becomes negative,
and `"\\u03bb"` becomes the text `u03bb`. The arbitrary-integer `N` suffix is
rejected. A compatible EDN adapter needs a corrected reader or an explicitly
restricted encoding. See the
[hedn source](https://hackage-content.haskell.org/package/hedn-0.3.0.5/src/lib/Data/EDN/AST/Parser.hs)
and [AST](https://hackage-content.haskell.org/package/hedn-0.3.0.5/src/lib/Data/EDN/AST/Types/Value.hs).

`kdl-hs` supplies a parser, renderer, and structured decoders. It is a credible
candidate for a KDL adapter. It adds Megaparsec and prettyprinter to this package's
direct dependencies and still needs the complete domain mapping. That is a
separate implementation, not a syntax switch. No compatibility or roundtrip
claim is made here. See
[kdl-hs](https://github.com/brandonchinn178/kdl-hs) and its
[package description](https://hackage-content.haskell.org/package/kdl-hs-1.2.1/kdl-hs.cabal).

## Current scope and follow-ups

Keep the small grammar-block codec for this PR. It shares the existing complete
value codec and validation, adds no parser dependency, and keeps the common
language example short. Its cost is a domain-specific syntax and a verbose full
form for complex constraints. Do not describe it as EDN or as a Redex frontend.
The roundtrip contract is between language values and canonical text; comments
and arbitrary input spelling are not retained.

Follow-ups, each with its own acceptance criteria:

- Add named pattern bindings that compile to existing path constraints. Check
  repeated and independent bindings, nested paths, and type errors. Retain each
  generated fact identity so that `relax` remains a natural operation.
- Add a data representation of `Update` and exact read/write support. Reopen an
  update, apply it to a typed source, and compare with the original expression.
  Distinguish reusable expressions from patches that require an exact old value.
- Compare a complete S-expression or corrected EDN adapter with grammar blocks
  on the same FTA, ECTA, and LTA examples. Include nested formulas, malformed
  values, large integers, Unicode, diagnostics, and parse/print costs. Do not
  add a second syntax that only covers the easy examples.
- Add a runtime/quasiquote definition interface that returns the same typed
  value. Resolve binding roles once, report source locations, and reject unknown
  states or facts before a query. Reuse the persistence parser where possible.
- Investigate named typing judgments over a stated supported fragment. Specify
  the translation to constraints and its completeness limits before promising
  enumeration. A later Lean export must represent this same fragment and its
  obligations, rather than omit unsupported premises.
- Keep binder declarations and alpha-equivalence separate from tree equality.
  Demonstrate capture-avoiding substitution before claiming binding support.

The first two follow-ups directly improve the concrete workflow. General macros,
unrestricted judgments, and host callbacks need separate capability boundaries.
