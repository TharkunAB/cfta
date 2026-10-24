# Changelog

## 0.1.0.0 - Unreleased

Before release, the package was called `microcfta-generator`.

Initial release. `cfta-generator` is one generator over the constrained
tree automata of `cfta`, with QuickCheck integration.

- `Data.CFTA.Gen`: one generator type, `Gen symbol a`, for every kind of
  automaton. An ordinary generator is `FTAGen symbol a`, that is
  `Gen symbol a`; the equality and refinement facades fix the symbol in
  `ECTAGen` and `LTAGen`. The sources are `elements`, `leaf`,
  `namedElements`, `fromIndexed`, and `fromGen`. `node` closes a constructor,
  and `frequency` and `oneof` choose. `match` and `relate` join two generators,
  and the grouped layer joins more with `Sig` signatures and `apply`. `recur`,
  `atomic`, and `upToSize` make and bound recursive languages. A recursive
  body composes its occurrence: a query of an unfinished occurrence reports
  `QueriedRecursiveOccurrence`, and a `recurGrouped` body that changes its
  keys or minimum sizes after discovery reports
  `InconsistentRecursiveFamily`. The exact
  inspectors are `cardinality`, `values`, `unrank`, `termAt` with its inverses
  `rankOf` and `ranksOf`, `support`, `inspect` with `drawInspection`, the
  counts by size, `pmf`, the structural `shrinkRank`, and `smallerMembers`. A
  generator keeps each construction failure as one `GenError`. `explain`
  describes it, and `orFail` fails with that text.
- `Data.CFTA.Gen` invertible blocks: `invertible`, `invertibleMap`, `invertiblePair`,
  and `rankOfInvertible` give the ranks of a value in a finite generator built
  from blocks that have an inverse. A choice, `pay`, `node`, and `atomic` keep
  the inverse. This is the term-to-rank map of a combinator generator.
- `Data.CFTA.Gen.Synthesis`: Hectare, the type-directed component
  synthesizer of the ECTA paper. `synthesize` lists the programs of a query
  by size, and `distinctProgramsIn` lists each program of a search space
  once (`programRuns` also marks each typed term); `programsOfSize` and `programsOfSizeUpToDepth` read the program
  space of a size as a generator. `rawSaturatedSearchSpace` builds the space of
  the saturated programs of a size, in which each head is applied to all its
  parameters, as in Hegel's terms. Hectare lists the programs of a space in
  the order of the rounds of the reduction, through `runsBy`: an edge that is
  in the space after an earlier round comes first, and the canonical order
  orders the edges of one round (`reduceWithOrder`, which gives a `Space`:
  the refolded automaton and the order). The order depends only on the
  automata, so it is the same in every process, also when the process built
  other spaces before. `programsIn`, `distinctProgramsIn`, and
  `programRuns` list a `Space`. `libraryEncoding` chooses how a space encodes the types
  (`Encoding`): `FirstOrder`, or `Curried`, in which a type constructor is
  a leaf applied by `@` edges, so that a type variable of kind `* -> *`
  (`?Foldable t0`) ranges over a domain of type constructors. Each key of
  the domains has its kind (`Domain`): a `HeadDomain` of type constructors
  of kind `* -> *`, or a `TypeDomain` of types. With `Curried OnlyDefault`
  (`Defaulting`), a variable of kind `* -> *` that a run does not determine
  takes only the list type, or none; a variable of a `TypeDomain` that a
  run does not determine gives one typed term. Marker leaves in the domains
  give both, and `runsNarrowedBy` of `cfta` reads them in each run. A
  domain type can refer to a domain (`List (?Ord x0)`); Hectare unrolls
  such a reference to one level, below which it takes any type.
  `parseType` and `parseProgram` read types
  and programs in Haskell syntax, and `renderType` and `renderProgram` print
  them. The `hectare` benchmark runs the paper's Hoogle+ and Stack Overflow
  suites. Their components and queries are in the public sublibrary
  `cfta-generator:hoogleplus` (`Data.CFTA.Gen.Synthesis.HooglePlus`), which
  the benchmarks and tests of this package and of `cfta-ghc` use.
- `Data.CFTA.Gen.Synthesis.Liquid`: Hegel, the refinement-typed component
  synthesizer of the LTA paper, with liquid qualifiers, the paper's prune,
  similarity, and minimization, conditionals at the goal, and function values
  applied by the measure `ap`. `parseRType` and `parseQuery` read refinement
  types and queries in the syntax of LiquidHaskell, and `renderRType` prints
  them. The `hegel` benchmark runs recreated versions of the paper's RQ1
  queries and its ablations.
- `Data.CFTA.Gen.Synthesis.Walk`: Hectare proposes, a host typechecker
  checks. `walk` builds, reduces, and lists Hectare's automaton of each size
  over erased leaves, each program of representatives once, and checks each
  program in preorder through a host's `Checker` (`checkerTruncate`,
  `checkerExtend`), from the prefix that it shares with the last one, with a
  trie of dead prefixes, limits, the time of each part, and the number of
  typed terms that Hectare listed (`progressRuns`). Because it keeps
  a set of the programs, not of the typed terms, the peak memory of the
  Hoogle+ ladder of `cfta-ghc` falls by 30% to 31% (45% to 46% on the
  queries that time out), with the same results and time. Its `Progress`
  tells how it ended (`progressOutcome`: `Solved`, `Exhausted`, or
  `OutOfTime`), and its caller says which fits are new (`hookNew`). The trie
  of dead prefixes is exported (`Dead`).
- `Data.CFTA.Gen.Synthesis.States`: mode (b), a search over states of a
  host's own goals, without Hectare and without erasure (`searchStates`). A
  state is the host's key of a goal, a size, and the query arguments to
  use; the host gives the refinements of a goal (`Goals`), kept by key and
  number of children, and the search walks the table in preorder and checks
  each complete program with the walk's `Checker`. With `Enumerated`, the
  table of each size is one cfta automaton, which cfta's enumerator lists in
  the host's order or in its own. The programs that Hectare's rule for the
  first argument drops leave the automaton (`excludeAnywhereFTA`), so its
  count (`figuresCount`) is that of the programs that remain.
- `Data.CFTA.Gen.Synthesis.Hybrid`: Hectare's program spaces with Hegel's
  checks. `synthesizeHybrid` lists the programs of the base types of a
  refinement-typed query size by size, in Hectare's order, in the saturated
  space, which has only Hegel's terms. It stops at the first one that passes
  `checker` or `preciseChecker` of `Data.CFTA.Gen.Synthesis.Liquid`. These
  check one program with Hegel's inference: the precise checker keeps each
  subprogram's refinement, and `checker` abstracts it to the qualifiers. With `hybridFallback`, on by
  default, Hegel's `synthesize` runs when the hybrid has no program within a
  time budget of 30 seconds. The `hybrid` benchmark runs Hegel and the hybrid
  on Hegel's queries and on a large library of the Hoogle+ components and
  refined list components.
- Sizes count pays, as in FEAT: `pure` has size zero, an atom one, `<*>` adds
  the sizes of its sides, and `pay`, which `Data.CFTA.Gen` and
  `Data.CFTA.Ranked` export, adds one. A constructor pays one, so a built tree
  and an imported term both count their nodes. The `Functor` and
  `Applicative` laws hold for sizes. A join (`match`, `relate`) adds the sizes
  of its sides, as a product does. Each integer of `every` adds one, as a
  member of `elements` does, wherever a constructor closes it. A recursion
  must reach each occurrence
  through a pay, or through a product whose other side has no member of size
  zero. It must also pass through a product or a constructor. See
  `docs/adr/0002-sizes-count-pays.md`.
- `Data.CFTA.Gen.QuickCheck`: `toGen`, `toGenWithRank`, `forAll` with
  size-minimal counterexamples, `sized`, and the frozen pools `samplePool`
  and `freeze`. `Data.CFTA.Gen.Do`: qualified applicative do-notation for
  every theory.
- Imported automata: `fromAutomaton` reads an acyclic automaton as a finite
  generator with one rank per distinct term, counted symbolically where
  alternatives overlap or equalities reach below direct children, and a
  cyclic automaton as a recursive generator counted by size. On the compact
  plan, the size of an imported term is its number of nodes: a group of
  equal children pays the size of its term once for each position. A
  symbolic count gives each term size one.
  `fromAutomatonUpToDepth` bounds first. `fromDatatype` and
  `fromDatatypeUpToDepth` read derived grammars of any theory, and report
  `UndecodableConstructor` when the codec rejects a term of the grammar.
  Ranks order the constructors at each node by arity, then by the symbol,
  or in declaration order for a datatype, so they are the same in every run.
  `rankOfTerm` gives the rank of an accepted term, and `rankOfValue` the
  rank of a datatype value through its codec.
- `Data.CFTA.Sized`: `termsOfSize`, `countOfSize`, `unrankOfSize`, and
  `rankOfSize` describe the distinct terms with `n` nodes that an explicit
  finite tree automaton accepts, as one sequence with inverse ranks. Each
  query ends, also on cyclic, ambiguous, and equality-constrained automata,
  and an empty class says nothing about later classes. `sizedReference`
  builds each class from smaller ones; `sized` gives the same sequence with
  the count table, read from the original rows, when the automaton has no
  constraint and no ambiguity. A guard
  beyond equality constraints is `ResidualGuard`. `sizedUpTo` builds the
  classes up to a size bound with a solver that decides every guard on each
  built term, so a liquid automaton has an exact route that needs no
  pruning; a guard the solver cannot decide is `GuardUnknown`.
- Terms are `Term symbol` from `Data.CFTA.Term` of `cfta`:
  `fromAutomaton`, `fromAutomatonUpToDepth`, `termAt`, `rankOf`, `ranksOf`,
  `rankOfTerm`, `surface`, and the refinement witnesses take and give `Term`
  terms in place of `Data.Tree.Tree`.
- `Data.CFTA.Gen.Equality`: `ECTAGen`, symbol-text order for imports,
  and equality constraints from `Data.CFTA.Equality`. The engine's
  `support` and `termAt` return graphs and terms over `Data.CFTA.Gen.Label`,
  which wraps user symbols in `Label` and types the private labels; a
  recursive member has a private `Recursion` root. `surface` reads the user's
  term back.
- `Data.CFTA.Gen.Refinement`: `LTAGen`. Its sources are `elements`, which
  infers the exact refinement of each integer; `every`, a leaf of every value
  of a type with a `Literal` instance, such as `Integer`, `Word8`, `Char`,
  `Bool`, or an enumeration; `pool`, of values with hand-written refinements;
  `namedPool`; and `leaf`. `checkPool` asks the solver to prove the
  refinements of a pool. `satisfying` puts a condition on a drawn child, and
  on `every` it narrows the values. The constructors are `node`; `guarded`,
  whose contract relates the children; and `refinedNode` and
  `refinedNodeByRoots` for the paper's positional guards and result
  refinements. `measured` closes a constructor with a contract and a measure:
  the integer of each constructed term, as a term of the measures of its
  children, which becomes the constructor's refinement and stays a term of
  children from `every`. A refinement whose defining term mentions the value
  itself, such as `v .== v`, gives no exact measure, and `compile` reports
  `InexactMeasure` for it, with the name of the measure and the positions of
  the children without one integer.
  `measuredNode` takes a positional guard in place of the contract.
  `measuredBy` gives a constructor several named measures: uninterpreted
  functions of the value, each one integer or one term of the integers of
  the leaves, which a contract reads as `uninterpreted name [child]`. A named
  measure of a child over `every` stays such a term, so `compile` counts it
  without enumerating the integers: the sorted lists of length 3 with keys up
  to a million and the named measures of their head and length count
  166,666,666,666,500,000 lists. A measure can choose with `ite`, `smaller`,
  or `larger`: when the children have one integer each, it takes the branch
  that the condition chooses, so the measure stays one integer. `recurUpTo` unfolds a recursive description a bounded number
  of times. The module also has liquid automaton and datatype imports,
  `minimizePoolOn`, `compile` with Z3, `compileAssuming`, `compileWith`, and
  `validOutcomes`.
- `Data.CFTA.Gen.Refinement.Derive`: refinement generators derived from a
  `HasFTA` datatype. `HasLTA` holds the node view of the datatype (`Node`),
  its measures (`Measures`), and an `Invariant`: a measure and a contract
  written once as functions that are polymorphic over `Symbolic`, over the
  node view, a datatype with the constructors of the datatype and the
  integers of their fields (`NodeView`). `deriveLTA` builds the generator
  that the combinators give, with their ranks, and reports a node view that
  does not fit the datatype (`NodeMismatch`): the shapes of the constructors
  differ, or the name of a constructor of the view does not start with the
  name of the constructor in its place (`checkNodeShape`). `nodeFields`
  reads the position of the constructor of a node and its fields. `Measured`
  has one measure,
  `Contracted` none, and `MeasuredBy` named measures, the fields of a record
  (`MeasureRecord`) whose selector names are the names in the logic. `holds`,
  `measureOf`, and `measuresOf` run the invariant on values, and
  `measuresAt` gives the measures of a value term. `deriveLTARooted` and
  `deriveLTAFromRooted` take a condition on the measures of the root, written
  once over `Symbolic`, and `holdsRooted` runs it on values. `atom` gives the
  generator of each atomic field type. `fieldAtoms` gives fields their own
  generators through the node view, with `drawnFrom` on a field that a node
  pattern binds, so two fields of one type can have two pools
  (`FieldAtomMismatch` and `FieldAtomTerm` for a pool that does not fit, and
  `FieldAtomOnDatatype` for a field of the datatype itself, which the
  invariant must check at each node). A
  contract conjunct about one atomic
  field becomes a condition on that field. A contract or a measure that reads
  a field whose type has no atom and no measure is `UnmeasuredField`. The
  module re-exports `Boolean`, `Symbolic`, `smaller`, `larger`, and
  `literal`.
- `Data.CFTA.Gen.Refinement.Derive.Internal`: the level below, exposed for
  integration and outside the PVP contract. `deriveLTAWith` takes the
  contracts and the measures of each `Constructor`, as annotations
  (`contract`, `measure`, `measureNamed`, `fieldsContract`,
  `fieldsMeasure`), and `annotationFormulas` gives their formulas and terms.
- `deriveLTAOn` and `deriveLTAOnFrom` in `Data.CFTA.Gen.Refinement.Derive`,
  and `deriveLTAOnWith` in its internal module, derive the refinement
  generator of the terms of an automaton over the constructors of a
  datatype, such as a typed language of `Data.CFTA.Gen.Typing`, so that the
  measures and the contracts of an invariant hold on its terms. Each state
  is a `oneof` of its transitions, and each transition is the generator of
  its constructor, as `deriveLTAWith` builds one over the field types. The
  ranks follow the generators. An automaton with a cycle gives
  `CyclicAutomaton`, and a transition with a constraint gives
  `ConstrainedTransition`.
- `Data.CFTA.Gen.Typing`: typed languages with variables, from typing rules
  for the constructors of a `HasFTA` datatype, written as nodes of its node
  view (`NodeView`), so a rule names its constructor and its fields by type:
  `rule (TAddNode (subterm [] TInt) (subterm [] TInt)) TInt`. `rule` gives a
  constructor a type from the types of its fields. `subterm` is a field in
  the environment of the node with some binders in front, `value` is a field
  with one value, and `variable` reads the environment by de Bruijn index.
  A `Typing` holds the bound (`Nesting` or `Binders`), the inputs, the root
  types, and the rules (`typingBound`, `typingInputs`, `typingRoots`,
  `typingRules`). `typingAutomaton` builds the explicit automaton over
  `Constructor` whose states (`TypingState`) are an environment, a type, and
  the nesting that remains, so that a caller can intersect, annotate,
  restrict, or exclude it as any `FTA`. `fromConstructorAutomaton` reads an
  automaton over the constructors of a datatype as a `Gen Symbol a` with the
  labels and the ranks of `fromDatatype`, and `fromTypingRules` is the two in
  one: the terms of the root types up to a bound on the nesting. The inputs
  are the variables in scope at the root, so the terms are programs over
  them. It reports a node view that does not fit the datatype
  (`NodeViewMismatch`), a rule that does not fit the fields of its
  constructor (`FieldMismatch`), and a negative bound (`NegativeBound`).
  `Data.CFTA.Gen.Typing.Do` writes the rules of a constructor in qualified
  do-notation, as premises (`sub`, `under`, `draw`), choices from lists (`each`,
  which can read earlier choices), conditions (`guard`), and a conclusion
  (`yields`); a block gives one rule for each combination of its choices.
  `drawn` makes a value field draw its values from a refinement generator,
  such as `every` with a condition, in place of one rule for each value.
  `Typing.Do` re-exports `drawn`; its `draw` statement gives the same field
  as a premise without listing the generator's values.
  `typingLTA` and `typingLTAFrom` (with an invariant) build the refinement
  generator of a typed language, and `compile` counts its drawn fields
  without listing their values; the plain builders report a drawn field as
  `DrawnField`. `deriveLTAOnPools`, in the internal derive module, derives
  over an automaton with the generators of some states given.
  With `Binders`, a bound on the binders around each position, and a rule
  with a `subterm`, the automaton is cyclic and the generator is counted by
  size; without a `subterm` rule it is acyclic and finite. A field
  that holds a subterm has the type of the datatype, so a family of mutually
  recursive types is not a language here.
  A fixed value in a field of the datatype gives `FieldMismatch`.
  Recursive fields must use `subterm` to check their environment and nesting.
  The ranks order the constructors of each type in the automaton in
  declaration order, as `fromDatatype` does. Literals have no declared
  position and follow the order of their labels. The positions come only
  from the types of the constructors of the automaton, so a field of a
  non-regular type that no rule uses does not stop the build.
- `compile` folds the recipe of a generator once with the solver. It groups
  child languages by the observations a guard reads, decides each guard once
  for each tuple of groups, and prunes and splits imports by the same
  observations without enumerating terms. It counts the values of `every`
  without enumeration, also under a linear contract over several such
  children. The result is an ordinary finite generator with exact counts,
  source-ordered ranks, and structural shrinking, and sampling makes no solver
  calls. A constructor that needs the solver, and an import whose guards the
  engine cannot count, defer the generator until `compile`. A bounded import
  whose guards pruning leaves uncountable reads its bounded denotation, with
  the solver deciding every guard on each term; only an unbounded one reports
  `ResidualGuard`.
- `Data.CFTA.Ranked`: finite ranks, weighted sampling, replay, and structural
  shrinking, independent of automata, with `Data.CFTA.Ranked.QuickCheck`.
- The engine modules `Data.CFTA.Gen.Internal.*` and the ranked internals
  `Data.CFTA.Ranked.Internal.*` are exposed for integration and stay outside
  the PVP contract.
- Two test suites, `gen-tests` and `refinement-tests` (needs `z3`), and one
  copy of the generator benchmark harness.
