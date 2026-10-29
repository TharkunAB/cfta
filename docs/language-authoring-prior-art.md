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
| Grammar blocks of `language 1;` | Common productions, refinements, facts, and exclusions are concise. | Maintain a small domain parser. Complex constraints use exact structural forms. |

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

## Edits, exclusions, and names

These sources compare with the edits, the exclusions, and the names of
`Data.CFTA.Language` and `Data.CFTA.Language.Source`.

- **Unit of an edit.** Ohm overrides a rule with `:=` and extends it with
  `+=`; `+=` is an error when the rule does not exist
  ([Ohm syntax](https://ohmjs.org/docs/syntax-reference)). Lark has `%extend`
  and `%override` for a rule
  ([Lark grammar](https://lark-parser.readthedocs.io/en/stable/grammar.html)).
  In ANTLR 4, a rule of the main grammar overrides an imported rule
  ([ANTLR grammars](https://github.com/antlr/antlr4/blob/master/doc/grammars.md)).
  In these tools, the unit of an override is a rule, that is, a state here. Ohm
  case names, Lark aliases, ANTLR labels, and Rascal labels name an
  alternative, but they name a node of the parse tree. None of these tools
  deletes one alternative by its name. A production name here is the key of
  an edit. The closest precedent is the merge key of a Kubernetes strategic
  merge patch, `patchMergeKey: name`
  ([kubectl patch](https://kubernetes.io/docs/tasks/manage-kubernetes-objects/update-api-object-kubectl-patch/)).
- **Exclusions.** SDF3 applies reject productions, priorities, and
  associativity as filters on the parse forest
  ([SDF3 disambiguation](https://spoofax.dev/references/sdf3/disambiguation/)).
  Afroozeh and others rewrite the grammar for precedence rules, and the
  rewritten grammar accepts the same language as the specification
  ([SLE 2013](https://link.springer.com/doi/10.1007/978-3-319-02654-1_8)).
  `Language.compileGraph` also rewrites: the exclusions become part of the
  automaton, so the compiled graph keeps exact counts, ranks, and sampling. A
  filter does not. In these sources, an exclusion has no name, and a change
  is an edit of the grammar text. Here an exclusion has a name, and
  `restore` removes it. Removal compiles the document and the other
  exclusions again; it does not undo a product.
- **Constraints.** ISLa attaches `forall` and `exists` constraints to a
  grammar and uses the Z3 solver to generate inputs
  ([ISLa](https://isla.readthedocs.io/en/latest/)). Fandango writes
  constraints in Python and searches for inputs that satisfy them
  ([Fandango](https://fandango-fuzzer.github.io/)). Neither compiles a
  constraint into the grammar, so neither gives an exact count. A fact here is
  a constraint of one production, with a name.
- **Stale checks.** A JSON Patch is atomic: when a `test` operation fails, the
  patch changes nothing ([RFC 6902](https://www.rfc-editor.org/rfc/rfc6902)).
  HTTP `If-Match` prevents a lost update, and it must use the strong
  comparison ([RFC 9110, section 13.1.1](https://www.rfc-editor.org/rfc/rfc9110)).
  A `Patch` compares the complete document, which is the strongest form of
  this check; its cost is a patch that holds the document. A JSON Merge Patch
  has no stale check ([RFC 7396](https://www.rfc-editor.org/rfc/rfc7396)), as
  an `Update` has none.
- **Names after a deletion.** Protocol Buffers reserves the numbers and names
  of deleted fields, because a reused number makes old data ambiguous
  ([proto3 guide](https://protobuf.dev/programming-guides/proto3/)). A
  document does not reserve a deleted production name: a new production can
  use it. A rank has no name or number, so a rank is valid only for the
  compiled graph that gave it.

## Current scope

Liquid Haskell is the primary inspiration for the constraint notation: refined
types, named measures, and explicit obligations. More complex, Lean-style
constraints are a future target. Neither resemblance in syntax nor the ability
to store a formula establishes complete type checking. See the
[Liquid Haskell specification reference](https://ucsd-progsys.github.io/liquidhaskell/specifications/)
and [Lean's introduction](https://lean-lang.org/doc/reference/latest/Introduction/).

The grammar-block codec builds typed values directly and uses the existing
graph and document validation. Its only parser library is attoparsec. It keeps
the common language example short. Its cost is a domain-specific syntax and structural
forms for complex constraints. Do not describe it as EDN or as a Redex frontend.
A printed language reads back equal, and printing it again gives the same
text. Only the `Notes` functions keep doc comments, and no reader keeps the
spelling of its input.

Later work can add named pattern bindings, a quasiquoter for definitions, and
typing judgments.
