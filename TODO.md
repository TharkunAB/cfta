# Not yet on main

This branch is `main` with every open pull request merged, and four commits
that have no pull request. This file lists that work. Remove an entry when it
is on `main`.

Each list is one stack of pull requests, from the bottom (based on `main`) to
the top.

## In progress: serialization

Each pull request is one complete feature. #188, the graph text format, and
#116, checkpoints, are on `main`. The others are drafts: mark the next one
ready when work on it starts.

Each of these pull requests needs the API of #116 when it is rebased on
`main`. `experimental` has these changes in its merge of `main`:

- `FTAError` has one parameter. A symbol can occur at several arities, so a
  language with a symbol at two arities is valid (#187: test and README).
- `mapSymbols`, `intersect`, and `intersectWith` are total.
- `exclusionText` and `exclusionParser` are the checkpoint forms. In #187, the
  language forms with names become `namedExclusionText` and
  `namedExclusionParser`, with the grammar rule `named-exclusion`.
- Remove the constraints that the new signatures make redundant.

- #110 `feature/source-documents`: Editable source documents and language updates
- #187 `feature/document-text`: Text forms of source documents, languages, and updates
- #126 `feature/document-merge`: Diff and three-way merge of languages by stable names
- #161 `feature/start-edit`: An edit that sets the initial state

## Not in progress

Each pull request in this section is a draft.

### Inclusion

- #101 `feature/language-inclusion`: Language inclusion up to a size, with a counterexample
- #103 `feature/exact-inclusion`: Exact language inclusion
- #105 `feature/constrained-inclusion`: Bounded inclusion for constrained automata
- #137 `feature/partition-check`: Check a partition of a language into parts

### Completions of a prefix

#102 conflicts with `main`.

- #102 `feature/grammar-mask`: Completions of a preorder prefix
- #108 `feature/completions-equalities`: Completions of a prefix with equality constraints
- #122 `feature/completions-guards`: Completions of a prefix with guards and a solver
- #138 `feature/weighted-completions`: Weighted completions of a prefix
- #157 `feature/lazy-guarded-completions`: Decide the guards of prefix completions on demand
- #159 `feature/completion-tokens`: Take the next tokens of a completions walk from its runs
- #164 `feature/equality-walk`: Decide the next tokens under equality constraints without listing

### Sized documentation

- #106 `docs/sized-row-order`: Sized: qualify the row-order claim

### Refinements over data

- #109 `feature/named-predicates`: Refinements over data: named sorts, predicates, definitions, and ground evaluation
- #128 `feature/theories`: Add theories: datatypes and structurally recursive definitions for every solver
- #133 `feature/z3-theories`: Decide the entailments of a theory with one Z3 process

### Template lowerings, trace languages, and extension checks

#112 conflicts with `main`. #120 and #127 both have #112 as their base.

- #112 `feature/template-lowerings`: Template lowerings
- #120 `feature/trace-languages`: Add Data.CFTA.Trace: trace languages of state machines
- #136 `feature/trace-operations`: Trace languages: determinize, concatenate, and project
- #140 `feature/trace-hiding`: Trace languages: hide steps in a projection
- #156 `feature/guarded-traces`: Guarded state machines: traces over named integers as a refinement generator
- #127 `feature/extension-checks`: Check a definitional extension, with counterexample terms
- #129 `feature/abstraction-checks`: Check an abstraction extension with a solver

### Lark export

#121 conflicts with `main`.

- #121 `feature/grammar-export`: Export a plain automaton as a Lark grammar
- #148 `feature/grammar-export-states`: Lark export: texts by state, brackets, and empty alternatives
- #150 `feature/grammar-export-order`: Lark export: an order of the children, brackets around another state, and lexemes

### Run-time signatures

#131 conflicts with its base, `feature/runtime-signatures`. GitHub shows no
checks for #134, #135, #142, and #191. A manual CI run passes on each.

- #125 `feature/runtime-signatures`: Typed languages from a signature that is data at run time
- #131 `feature/value-sorts`: Value sorts in run-time signatures, counted without listing the values
- #134 `feature/signature-binders`: Binders and variables in run-time signatures
- #135 `feature/signature-refinements`: Refinements and preconditions in run-time signatures
- #142 `feature/refined-pools`: Pool value sorts on the refined route of run-time signatures
- #191 `feature/signature-data`: Run-time signatures: the data in cfta, and a check of the sorts of states

### Learned exclusions and named holes

- #139 `feature/learned-exclusions`: Learn exclusion templates from rejected and accepted terms
- #153 `feature/named-holes`: Add named holes to templates, with exact named exclusion

### Edits

"Format and lint" fails on #141 and on each pull request above it.

- #141 `feature/edit-automaton`: The edit automaton of a term
- #146 `feature/edit-sets`: Edit sets: edits at up to k incomparable sites of a term
- #151 `feature/edit-primitives`: Edits: unwrap a subterm, and wrap it in a context with one hole
- #152 `feature/edit-trees`: Edit trees: edit sets where an edit may lie inside a wrap
- #155 `feature/edits-between`: editsBetween: the edits that give a new term from an old one
- #158 `feature/constrained-edits`: The edits of a term under equality constraints
- #160 `feature/guarded-edits`: The edits of a term under guards, with a solver
- #162 `feature/edit-trees-canonical`: Edit trees: one context wrap instead of stacked wraps
- #163 `feature/edit-sets-between`: editSetsBetween: the edit sets that give a new term from an old one

### Invertible generators

"Format and lint" fails on #144.

- #143 `feature/invertible-generators`: Invertible generator blocks: term to rank for combinator generators
- #144 `feature/invertible-compile`: Rank a term in a compiled refinement generator by its surface

## Commits without a pull request

- `b2a4b10e1`: `tableIndexes` takes the leaf sources of `tableIndex`. The
  completions stack adds `tableIndexes`, and the run-time signatures stack
  adds the leaf sources. Add this change to the stack that is merged second.
- `40f13e60d`: the text forms of named predicates and named sorts. This needs
  serialization and #109 on `main`.
- `39c500494`: named holes `_name` in the text form of templates. This needs
  serialization and #153 on `main`.
- `fb974cc3a`: signature files (`signature 1;`, `printSignature`), and a test
  that checks the sorts of a graph read from text with `checkSorts`. The
  sorted states of this commit are now in #188 and #187. This needs #191 on
  `main`.
