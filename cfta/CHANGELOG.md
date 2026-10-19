# Changelog

## 0.1.0.0 - Unreleased

Before release, the package was called `microcfta`.

- `Data.CFTA.replaceRows` applies row replacements and deletions to an
  existing explicit automaton. It shares unchanged rows and validates the
  complete result after the batch. The original automaton stays unchanged.
  The operation works for ordinary, equality, and liquid annotations.
- Template exclusion removes incompatible positive requirements and choices
  that require the same child pattern to both match and fail. It preserves
  the order and obligation lists of the surviving split choices.
- `Data.CFTA.Enumeration` adds an optional ordered cursor with caller-defined
  keys and admissible partial bounds. It supports monotone shared pruning,
  explicit resumable work and frontier limits, and queue statistics. Existing
  enumeration entry points keep their defaults. The callback contracts state
  the remaining proof obligation for constrained cyclic truncation.
- Add `Data.CFTA.Document`: editable source documents with named
  productions and named facts, and patches that check the document they
  were prepared on.
- Add `Data.CFTA.Language`: updates that combine with `<>` over a source
  document, and named exclusions that `restore` removes again.
- Add `Data.CFTA.Lowering`: template lowerings, which translate the terms of
  a language version to the version before it. `lift` gives the inverse image
  of an automaton, and `checkLowering` checks a later grammar against an
  earlier one. `compose` makes one lowering of two. It reports an expansion
  that applies an earlier constructor to the wrong number of children.
- `Data.CFTA.Refinement.Expression.modulo`: the remainder of a term, as the
  `mod` of SMT-LIB.
- `refoldEdges` is `refold` with the edge of the result that each edge of
  the input becomes, so that a caller can carry data about the edges of a
  graph through `refold`, whose new edges have new identities.
- `Data.CFTA.Generic` exports the constructors of `Description`,
  `AtomicType` and `AlgebraicType`, so that another module can read the
  constructors and the field types of a datatype.
- `Data.CFTA.Refinement.Symbolic`: the classes `Boolean` and `Symbolic`. They
  give the operators of the refinement logic on values (`Integer` and `Bool`)
  and on terms (`Expr` and `Formula`), so one polymorphic function is both a
  predicate and a refinement. `ite` chooses one of two integers by a truth
  value, and `smaller` and `larger` come from it.
  `Data.CFTA.Refinement.Expression` exports `conditional`, the choice on
  terms.
- `Data.CFTA.Refinement.Symbolic.Internal`: `Measures`, the children of a
  constructor, a term on `Expr` and the integers of a node on `Integer`, with
  `childMeasure` for a named measure of a child: the backend of the derived
  refinement generators of cfta-generator, exposed for integration and
  outside the PVP contract.
- Expose constructor rows before path traversal, equality edits, and template
  restriction of recursive nodes. Retained empty recursive cycles now return
  empty instead of repeating the same unfolding request.
- `Data.CFTA.Template.exclude` keeps exactly the terms of an interned graph
  that match none of some templates at the root, as `matchesNone` says. It
  splits an edge by what its children match, so an unambiguous input gives
  an unambiguous result, and counts and ranks over it are exact. It reaches
  only as deep as the templates. A split that keeps two different parts
  without holes at one child has no terms, and it is left out, so the
  preorder prefixes of a trie give a child one copy for each part that they
  fix there and one for none, not one copy for each subset of the prefixes.
  `excludeFTA` does the same for an explicit-state automaton: each result
  state pairs a source state with an `Obligation`, the templates that its
  terms must match and those that they must not.
  `excludeAnywhere` and `excludeAnywhereFTA` keep the terms of which no
  subterm matches one of the templates (`matchesNowhere`), with a recursive
  result for a recursive input, and `preorderPrefix` gives the template of a
  prefix of a term in preorder.
  `excludePrefixesFTA` keeps the terms of an explicit-state automaton whose
  preorder starts with none of some prefixes, as `excludeFTA` of their
  `preorderPrefix` templates does, with the same runs. A result state pairs a
  source state with two `Position`s in the minimal automaton of the
  prefixes, not with a list of templates.
  `Data.CFTA.Interned.fromRows` interns the transitions of each state as
  `fromFTA` does, without a ranked alphabet.
- `fromFTA` and `fromRows` nest the binders of a strongly connected
  component in one order, the order in which a depth-first walk from the
  initial state meets the states. A node is then built once for each set of
  enclosing binders, at most 2^k for a component of k states, instead of
  once for each order of them, about e * (k - 1)!. On the products of
  `excludeAnywhereFTA` with a component of 9 states, `fromFTA` took 3.6 s at
  -O0 and takes 16 ms. The terms and their runs do not change.
- `exclude`, `excludeFTA`, `excludeAnywhere`, and `excludeAnywhereFTA` keep a
  template alive into a child only when the child can match its part, with
  the other parts that it must match, at the root of one of its edges. A
  part that no edge of the child fits is not passed to the child. On a cell
  of Specftacular's lists-5-1 whose templates all have the root `app`, the
  split at the function child made 3,521 copies and 190 states (1.4 s at
  -O0); it now makes 10 copies and 10 states (5 ms). The terms and their
  runs do not change.
- Fix `reducePartially` not returning when a node at the end of an equality
  path reaches a recursive node with constraints. The intersection at that
  path unfolded the recursive node, a narrowed child contained its own
  ancestor, and the memo demanded its own unfinished result. `termsMatching`,
  the README's `fixUnbounded (withoutRedundantEdges . reducePartially)`, and
  Hectare's `reduceFully` inherited this. Such a class now stays unreduced.
  Enumeration and `accepts` still check it, so the language does not change.
- Add `provablyEmpty`, a sound check that a closed node accepts no term: a
  least fixed point over the node's children and the intersections of its
  equality classes, within a budget of nodes. When the endpoint rule of
  `reduceEqConstraints` leaves a class unreduced and the check proves the
  intersection at its paths empty, the edge becomes empty. On the input of the
  previous entry, `reducePartially` now returns `EmptyNode`.
- The check of the previous entry also covers a class whose path ends at a
  closed recursive node with constraints, such as the input of the entry
  before it without its wrappers, `p(A, C)` with `0 = 1`: `reducePartially`
  returns `EmptyNode` for it too.
- Fix `terms` and `runs` not ending on the input of the previous entries. The
  enumerator merges the two children of the class into one variable, and the
  intersection `W(A) ∩ W(C)` is `W(R)`, which needs R again. When a merge
  intersects two nodes and the result reaches a recursive node with
  constraints (`reachesConstrainedMu`, now exported), the enumerator runs
  `provablyEmpty` on it, memoized, and ends the branch when it is empty. No
  term is lost, because the branch has none. `terms R` now gives `[]`.
- Fix `reducePartially` and `termsMatching` using more than 8 GB on an
  automaton of two states, through the check of the previous entries.
  `provablyEmpty` intersected the intersections of its requirements. Each
  such intersection is a new node, deeper in recursive nodes than its
  operands, and the cost of an intersection grows with that depth. The check
  now reads conjunctions: sets of nodes that one term must be in, whose edges
  it reads together. Two conjunctions of the same nodes are one conjunction,
  so the fixed point closes. On the input that the seed 38593640 of the
  property "restrict to a template as filtering the terms by the template
  does" gives, a copy of the check read 11 nodes in 0.6 s, and the
  intersection for the next node did not end in a minute. The new test of
  that input, `termsMatching` and `terms` up to the depth 3, takes 12 ms.
  The answers on the inputs of the previous entries do not change.

Initial release. `cfta` consolidates an ordinary tree automaton engine,
equality-constrained tree automata, and liquid tree automata into one package
with one representation. The equality layer descends from `microecta`, which
remains a separate ECTA-only package.

- `Data.CFTA.Formula`: the refinement logic. A formula is `Top`,
  `Bottom`, a comparison of two terms, a conjunction, disjunction, or
  negation, or a quantifier over sorted names. Terms have integer
  arithmetic with division and modulo, casts, and uninterpreted functions.
  A `Symbol` holds a formula, and only the Z3 entailment translates it to
  Liquid Fixpoint.
- `Data.CFTA` and `Data.CFTA.Interned`: the explicit-state and interned
  automata. The interned automaton has one `Constraint` on every edge, and
  the explicit-state automaton has an annotation parameter. Ordinary automata use `noConstraint`.
  Recognition, depth bounds, product intersection, union, templates, paths,
  datatype derivation with `HasFTA`, constructor annotation by name with
  `annotateConstructors`, and level-by-level enumeration with
  `terms` and `termsUpToM` are in these modules. A `union` inside a binder
  keeps a reference to an enclosing binder as a union node until the binder
  closes; a binder's reference to itself at the root of its body adds no
  term. A binder probes its body with a placeholder above every placeholder
  that the body captures, so a closed nested binder does not wait on a
  reference it captured.
- `Data.CFTA.Equality`: equality-constrained automata as
  `Node symbol` with `equalityConstraint` edges, with reduction, membership, template
  restriction, and enumeration with unification variables. An automaton with
  no constraint and no recursion is listed level by level, without
  unification variables. The enumerator keeps the variables that it can
  expand and the variables that suspended constraints wait for, so a step
  does not scan every variable; on Hectare this cut 11% of the allocation.
  The enumeration monad passes continuations instead of building a list of
  branches at each bind; on Hectare this cut 32% of the listing time. The
  suspended constraints of an edge go to all its children in one pass,
  which cut a further 8%.
- `Data.CFTA.Refinement`: liquid tree automata as
  `Node Symbol`, built with the interned constructors;
  the module re-exports `Data.CFTA.Interned`. It has the paper's Boolean guard
  language, actual-for-formal position substitution, transition-level semantic
  pruning, similarity (`similarityWithin` asks only about transitions of one
  class), minimization, recursive nodes under the acyclic-guard
  restriction checked by `validate`, a bounded reference denotation on the
  shared enumerator, and the Z3 entailment in
  `Data.CFTA.Refinement.LiquidFixpoint`, which declares every free name as an
  integer, and a free name that a query applies to arguments as a function
  from integers to an integer. A fresh value name of a binding must not be a declared name or a
  free name of an ambient assumption; otherwise the query is `Unknown`.
  Every name reaches Z3 through one injective encoding, so two distinct names
  never become one SMT name.
  `Data.CFTA.Refinement.Guard` builds transitions from guards that
  name the constructor arguments, `contract` states a formula about the
  children's values, and `measureTerm` reads the measure of a constructed
  term from the measures of its children.
- `Data.CFTA.Refinement.Expression`: the refinement logic. A refinement is a
  Haskell function of the value, as in `\v -> v ./= 0`. Terms take integer
  literals and arithmetic through `Num`; the comparisons are `.==`, `./=`,
  `.<`, `.<=`, `.>`, and `.>=`, and the connectives are `.&&`, `.||`, and
  `lnot`. `uninterpreted` applies an uninterpreted function, such as a
  measure, to terms. `Formula` is the closed formula that the engine stores, and
  `refinementFormula` gives the formula of a refinement about the value
  variable, the reserved name `valueName` of `Data.CFTA.Symbol`. `Literal`
  gives the integer that stands for each value of a type, the value of each
  integer, and the range of a bounded type. It has instances for integral
  types, `Bool`, `Char`, `Ordering`, and `()`, and for enumerations through
  `Enumerated`. `literal` writes a value as its integer on any `Num`: a term on `Expr`, and the integer on `Integer`. `substitute` replaces named values by terms,
  `definingTerm` reads the term of a formula `v .== t`, and `freeNames` lists
  the names of a formula. `substitute` renames a bound name together with the
  nullary applications that refer to it, and it replaces a function head only
  by a name. A replacement of a function name by another term leaves its
  applications as they are, and `substituteChecked` reports it.
- `Data.CFTA.Refinement.Lattice`: the exact number of integer points of a
  linear formula over bounded variables, the point at each rank in
  lexicographic order, and the rank of each point, without enumeration. The formula becomes a signed sum
  of conjunctions, and the variables are summed out with Faulhaber
  polynomials. `onlyPoint` reads the one integer that a formula admits.
  `latticeEntailment` is an `Entailment` without a solver: it counts the
  integer points that satisfy the antecedent and falsify the consequent, and
  answers `Unknown` for a formula it cannot count.
- `Data.CFTA.Enumeration`: one enumerator for every theory. `terms` solves
  path equalities by unification and stops at recursion, `plainTerms` lists an
  automaton without constraints lazily by depth, and `runs` returns each
  accepting run with the residual constraints it must satisfy. The pruning
  oracles are `termsPrune` and `termsPruneWith`. The enumerators list the
  edges of a node in a canonical order: by arity, then by symbol, then by the
  canonical classes of their children (`canonicalClasses` of
  `Data.CFTA.Interned`), then by their constraint. So the order of the terms
  does not depend on the order in which the process interned the edges.
  `runs`, `truncatedTerms`, `termsPrune`, and `termsPruneWith` need
  `Ord symbol` for this. `runsBy` lists the runs of `runs` with a weight for each
  edge: it tries the edges of a node with larger weights first, and edges
  with equal weights in the canonical order. `runsNarrowedBy` also applies
  a function to the edges of each node of a run before it tries them.
  `runsInterned` lists the runs of `runs` in the order of the edges in the
  automaton, without the canonical classes, for a caller that sorts the runs
  itself. `edgeIdentity` of
  `Data.CFTA.Interned` gives the interned identity of an edge.
- `Data.CFTA.Simple`: the automata defined as simply as possible, on the
  explicit-state automata of `Data.CFTA`. Membership recurses on the term,
  the terms up to a depth are every accepted tree of the underlying graph,
  and union, intersection, and the depth bound are the textbook
  constructions. The tests check the interned automata, enumeration, the
  reductions, and the liquid automata against it.
- Enumeration removes duplicate terms with a hash set, so `terms` and
  `termsUpToM` of `Data.CFTA` need `Hashable symbol`. With an optimized
  `hashable`, this takes less than half the time of an ordered set on the
  ambiguous enumeration benchmarks.
- `Data.CFTA.Symbol`: one interned `Symbol` type for every layer. A symbol is a
  text and a refinement, which is `PTrue` for an ordinary symbol.
  `RefinedSymbol` builds and matches a refined symbol, and `symbolText`,
  `symbolRefinement`, `unrefined`, and `eraseRefinements` read and edit it.
- Each equality class caches its hash, and path tries hash without a list
  conversion, so interning an edge no longer rehashes its constraint's trie.
  Class completion in `mkEqConstraints` is an in-package union-find, which
  removes the `equivalence` dependency. Over the core benchmark suite this
  cut allocation by 46% and instructions by 41%. The unfolding of each
  recursive node is shared, so repeated listings of a `Mu` do not rebuild it.
  The intersection memo interns its recursive environment, the common
  `Symbol`/`EqConstraints` instantiation has its own memo tables, and the
  equality reduction restricts and edits every required path of an edge in
  one traversal, which cut a further 15% of instructions and 17% of
  allocation on that suite. An `EqConstraints` value is interned, so its
  equality and hash take constant time, and its descent into a child is
  memoized; on Hectare this cut 4% to 7% of instructions. The edge and node
  intersection memos keep integer keys in an open-addressing table,
  `Data.CFTA.Interned.FlatMemo`, in place of a hash map; on Hectare this cut
  24% of the time of two reduction rounds and 11% of the listing time.
  The enumerator keeps the count of the suspended constraints that wait for
  an equality class by the class's representative, so a step no longer
  resolves every waiting variable through the union-find, and a write of a
  slot changes only the counts that change. On Hectare's listing of
  headLast at size 5 this cut 13% of instructions and 9% of allocation.
  The value slots of the UVars are an `IntMap`, not a `Seq`, and the hot
  fields of the enumerator's state are strict, which cut a further 9% of
  instructions and 8% of allocation on that listing.
- The refinement layer's `denotationAtMost` runs on the shared enumerator: a
  positive `Same` guard is a path equality solved by unification, so an
  equality-guarded pair costs milliseconds instead of a quadratic candidate
  filter, and an unconstrained bounded automaton is listed without interning.
- `Data.CFTA.Interned.fromFTA` imports a recursive graph as `Mu` nodes, and
  `boundDepth` bounds an interned graph by tree depth;
  `Data.CFTA.Enumeration.plainTermsAtMost` lists a graph up to a depth without
  building the bounded graph. The reduction in
  `Data.CFTA.Equality.Operations` narrows children by the `equalities` of any
  constraint.
- LTA pruning narrows equal positions to their intersection through that
  reduction, specializes nodes bottom up and shares each result by node
  identity, and prunes a recursive node to a fixed point. Each of these fixed
  points takes at most 64 passes (`pruneRounds`), so pruning always ends; when
  a budget runs out, the automaton keeps the guards it has not discharged,
  and its language does not change. It keeps an edge
  whose guard the sparse evaluation cannot decide: two actuals with the same
  name and refinement, which can be equal or different terms, whose name an
  enclosing substitution scope renames. It also keeps an edge where such an
  actual replaces a formal name by itself before a non-identity replacement
  of that name in the same scope. Each Boolean operand of a guard has its
  own substitution scope, and a combined guard flattens, sorts, and removes
  duplicate conjuncts. Minimization runs
  the paper's M-Trans on the explicit view and interns the result. It keeps
  the representative of the root's class at the root. There is no
  separate state type, syntax module, or lowering to an equality automaton:
  residual positive equalities stay on the transition as its `equalities`.
- One vocabulary across the layers: membership is `accepts` (`acceptsWith`
  on the interned engine takes the constraint interpreter), the equality
  theory's constraints are in `Data.CFTA.Equality.Constraint` beside the
  equality facade, the bounded denotation reports a `DenotationError`, and
  both theory facades re-export the engine, the paths, the enumerator, and
  the templates.
- `Data.CFTA.Constraint`: one `Constraint` data type for every kind of
  automaton: path equalities (`constraintEqualities`) and a `Guard`
  (`constraintGuard`). `noConstraint`, `equalityConstraint`, and
  `semanticConstraint` build one, and `conjoinConstraints` conjoins two. A
  guard (`Satisfies`, `Holds`) adds a constraint that a solver decides.
  `PlainFTA` is `FTA state symbol Constraint`, and an ordinary automaton has
  `noConstraint` on every transition. `indicators` reads a constraint as a
  signed sum of equality indicators. The symbolic counter of the generator
  uses it to count Boolean equality guards without the solver.

### Differences from microecta 0.1.0.0

- The type of an ECTA is `Node symbol`; there is no separate
  ECTA node type. `edgeEcs` is `edgeConstraint`, a `Constraint`, and the FTA views return
  `FTAViewError`.
- Concrete terms are `Term symbol` from `Data.CFTA.Term`: a symbol with
  its children in a constructor chosen by the arity (`Leaf`, `One`, `Two`,
  `Three`, and `Many` with a `Seq` of four or more children), so a path
  reads a subterm with one field read or one `Seq.lookup` per step. The
  module does not export the constructors. The pattern `Node` builds and views
  the children as a list, as `Data.Tree.Node` does, and `fromRoseTree` and
  `toRoseTree` convert to and from `Data.Tree.Tree`. `Ord` and `Hashable`
  agree with `Data.Tree`, so the orders of `terms` and `fromTerms` do not
  change; a term shows as `Node symbol [children]`. Every function that
  takes or gives a term uses this type: `accepts`, `acceptsM`, `fromTerms`,
  `terms`, `termsUpToM`, the enumerators of `Data.CFTA.Enumeration`,
  `equalitiesHold`, the codecs of `Data.CFTA.Generic`, the refinement
  evaluation and denotation, `Data.CFTA.Simple`, `eraseRefinements`, and
  `matchesTemplate`. The
  automaton views of `toTree` stay `Data.Tree.Tree`, for `drawTree`. Partial
  or truncated enumeration uses `PartialSymbol symbol` rather than inventing
  symbols in the caller's alphabet.
- The hash-consing and memo tables are immutable maps updated atomically, so
  building automata from several threads is safe. Edge joins are keyed on the
  symbol itself rather than on its hash.
- `terms` truncates at recursion and lists an unconstrained node through
  the shared enumerator, so each such term appears once.
- `reduceEqConstraints` makes one pass over an edge's classes, as in the ECTA
  paper. In `microecta` it repeats the pass until the children stop
  changing. Each new pass reads new nodes and misses the intersection memo,
  so that fixpoint made the term search of the ECTA paper (Hectare) about
  100 times slower. One pass can leave children that a second pass narrows
  further: iterate
  `reducePartially`, as `reduceFully` does, to get a fixpoint. `prune`
  iterates the reduction of each transition. The reduction narrows a path by
  the merged nodes at the other paths of its class (`mergeAlternatives`):
  more than four edges with one symbol become one edge, so the narrowing can
  keep more terms but no fewer, and an intersection no longer pairs every
  edge with every edge of the same symbol. A child union that holds a
  recursive or a union node is not merged further, so the merge of two
  recursive languages ends. On Hectare this makes two rounds of a size-7
  query about 50 times faster. Such a child union stays a union node, so a
  later pass does not unfold it again, and repeated equality reduction and
  pruning reach a fixed point.
- The term-search application layer is not part of the library.
- The `Pretty` class and the path-trie `Ord` instance are gone; `show` the
  constraint, or compare equality classes by their path lists.
- The Z3 entailment declares the names of a scope once, when it starts a Z3
  process, and each query declares only its fresh names. A query sends about
  a third less text, and the Hegel queries take about 8% less time with the
  same answers.
