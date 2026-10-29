# Glossary

The words this repository uses for its domain, with the words of the sources
where they differ. Sources: the ECTA paper (Koppel et al., *Searching
Entangled Program Spaces*, ICFP 2022) and the `ecta` library; the LTA paper
(*Liquid Tree Automata*, arXiv:2605.13456); TATA (Comon et al., *Tree
Automata Techniques and Applications*); CLRS (union-find); Nijenhuis and
Wilf, and Feat (ranking).

## Terms and automata

- **Term**: a tree of symbols.
- **Arity**: the number of children of a symbol or a transition. All sources
  say arity.
- **Path**: the child indexes from the root of a term to one of its nodes.
  TATA and the LTA paper call this a *position* (`Pos(t)`, `t|p`, `i.j.k`);
  ECTA calls it a path. In this repository the list is a path. "Position"
  has its plain meaning: the place of one item in a sequence, such as a
  child among the children of a node, or a member in its size class.
- **Child index**: one step of a path: the zero-based position of a child
  among the children of a term node or a transition. The LTA paper says
  *position index*.
- **Transition**: a rule `f(q1, ..., qn) -> q`. An **edge** is a transition
  of an interned automaton (the `ecta` library's `Edge`; the ECTA thesis says
  *hyperedge*). A **transition index** selects one transition of a state or
  node.
- **Node, state**: a node of an interned automaton is a state; ECTA uses both
  words for one thing.
- **Node identity, edge identity, symbol identity**: the identity that
  interning gives a node, an edge, or a symbol. The three are different
  types; the `ecta` library has one `Id` for all three.
- **View, view path, view step**: a tree view unfolds a graph; a view path
  locates one occurrence in it; each step is a transition index, then a
  child index.
- **Depth**: the longest root-to-leaf path of a term, in edges; a leaf has
  depth 0. TATA's *height* counts a constant as 1, so height = depth + 1.
  **Mu depth** is the nesting depth of `Mu` binders, a different quantity.
- **Graph snapshot**: a stored explicit graph with its symbols, refinements,
  constraints, states, and transitions.

## Constraints

- **Equality class**: a set of paths that must hold equal subterms (ECTA:
  *path equivalence class*, PEC; type `PathEClass`).
- **Equality constraints**: the equality classes of a transition (ECTA:
  *path constraint set*, PCS; type `EqConstraints`).
- **Guard**: the formula on a transition: equal terms at two paths,
  refinements that a path satisfies or entails, formulas over the terms at
  paths, substitutions, and Boolean connectives. The LTA paper calls this the
  transition's *constraint* `ψ`.
- **Constraint**: the whole label of a transition: equality constraints and
  a guard.
- **Contract**: a guard about the children of a constructor, written as a
  function with one term for each child, in order.
- **Measure**: the integer of each term of a constructor, written as a term
  of the measures of its children (`measured`). The refinement of a constructed
  term is `v == measure`, so the contract of a parent reads it. Liquid Haskell
  says measure; the LTA paper calls a constructor's refinement its *result
  refinement*.
- **Observed**: what a guard can read at one path of a term: the symbol there
  and its **leafness** (leaf, inner, or mixed when some members of a group
  are leaves and some are not).
- **Similarity pair**: two transitions where the first (the **subtype**)
  refines the second (the **supertype**); the LTA paper writes `δi ≲ δj`.
  Minimization keeps the **representative** and removes the supertype.

## E-graphs

- **E-graph**: a set of terms with a congruence of them, as in egg
  (`Data.CFTA.EGraph`). An e-graph is a bottom-up deterministic tree
  automaton.
- **E-class**: a set of equal terms of an e-graph; a state of its automaton.
  An e-class is not an equality class, which is a set of paths.
- **E-node**: a symbol with an e-class for each child; a transition of the
  automaton of an e-graph.
- **Sort**: the term, such as a type, that each e-class of a sorted e-graph
  has. Sorts never merge. An ECTA of typed terms puts the type in a child
  instead.
- **Pattern**: a term with variables and sort variables. A variable that
  occurs twice is an equality class of paths.
- **Match**: an e-class of an instance of a pattern, and an e-class for each
  variable of the pattern.
- **Rule**: a left and a right pattern; each instance of the left side is
  equal to the instance of the right side.
- **Equality saturation**: the application of rules to an e-graph until no
  rule changes it, or a limit stops it.
- **E-class analysis**: data for each e-class, the merge of the data of its
  e-nodes, a bottom-up evaluation of the automaton of the e-graph. A
  **condition** of a rule reads it. A refinement of the value is such data,
  and its merge is the meet, because the terms of an e-class have one value.
- **Stamp**: the iteration of the last change of an e-class. **Semi-naive
  matching** finds only the matches through e-classes with a stamp after the
  last run of the rule.

## Transformations

- **Exact transformation**: an operation on an automaton that keeps its
  language, the set of terms it accepts. Equality reduction
  (`reducePartially`), `prune`, `withoutRedundantEdges`, `refold`, and `trim`
  are exact. A path that lists, counts, or ranks accepted terms, such as the
  generator imports, uses only exact transformations.
- **Over-approximation**: an operation whose result accepts every term of
  its input and possibly more, such as `mergeAlternatives` and
  `dropConstraints`. It enters an exact path only where the caller checks the
  original constraints again: the narrowing set of `reduceEqConstraints` is
  merged, and enumeration and `accepts` still check each equality class.
- **Representative selection**: `minimize` replaces a transition by the
  representative of its similarity class, so the result can accept fewer
  terms. No exact path uses it. The user applies it: to a pool with
  `minimizePoolOn`, or as the last step of the paper's reduction, `reduce`,
  which keeps the most specific term of each refinement, as a synthesizer
  needs.

## Ranking and sampling

- **Rank**: the zero-based index of a term or value in the enumeration
  order. **Unrank** is its inverse (Nijenhuis and Wilf). Not the CLRS rank
  of a union-find tree.
- **Cardinality**: the number of members of a language (Feat).
- **Size**: the number of pays of a generated member, as in FEAT: `pure` has
  size zero, an atom one, a product the sum of its sides, and a pay, such as
  a constructor, one more. For an accepted term, the number of its nodes. A
  **size class** holds the members of one size.
- **Class rank**: the rank of a member inside its size class. A **sized
  rank** is a size with a class rank.
- **Rank offset**: the first rank of a group of members in a larger
  language.
- **Weight**: a relative frequency weight of an alternative or a value
  (QuickCheck's word). Not the real-valued weight of a Boltzmann sampler.
- **Checked rank**: a rank of a term with whether the ranking checked every
  symbol of the term.
- **Occurrence**: the token of one recursion probe.
- **Exclusion**: a template that rejects a term, when the whole term matches
  it (at the root) or when a subterm matches it (anywhere).
- **Query route**: a named way to list the terms of a language, with a version.
  The language is a graph and its exclusions: the terms of the graph that no
  exclusion rejects. The route and its version fix the order. Route `sized`,
  version 1, is the order of `Data.CFTA.Sized`. A **listing** holds the terms
  of each size from one to a size bound, in the order of a route.
- **Checkpoint**: a saved position in a listing: the graph, the exclusions, the
  query route and its version, the size bound, and the sized rank of the next
  term. Resuming a checkpoint gives the next term and the terms after it, in
  the same order, also in a new process. A checkpoint is **stale** for each
  graph other than its own graph, and for other exclusions.
- **Relocation**: finding a term in another graph, and making a checkpoint at
  that term. It does not continue the old listing: the new listing can repeat
  or skip terms of the old one.
- **Sampled run**: the terms that a sequence of draws from a listing gives,
  one term for each draw. Draw *i* depends only on the seed and on *i*.
  Without weights, each term of the listing has the same chance. With weights,
  a draw selects a size by its weight, then a term of that size.
- **Sampling checkpoint**: a saved position in a sampled run: the graph, the
  exclusions, the route and its version, the size bound, the weights, the
  pseudorandom generator (PRNG) and its version, the seed, and the number of
  draws so far. It is stale for each graph other than its own graph, and for
  other exclusions or other weights.

## Generators

- **Choice index**: the position of an alternative in a generator choice.
- **Component index**: which component of an n-way join.
- **Argument index**: the position of an argument of a join, a guard, or a
  contract.
- **Group index**: which matched key pair of a two-way join.
- **Key index**: the position of a key among the keys of a recursive family.

## Variables

Three kinds, never called only "variable":

- **Union-find variable** (`UVar`): a variable of the enumeration; each set
  has a **representative** and each other element a **parent** (CLRS).
- **Variable index** (`VarIndex`): the position of a variable in the
  variable list of one problem (the symbolic counter, the lattice counter,
  the open integer variables of a compiled group).
- **Recursion reference** (`RecNodeId`): the variable that a `Mu` binds.

## Language chains

- **Language chain**: a sequence of language versions L0, L1, ..., Ln. Each
  version comes from the version before it by one extension or one
  restriction.
- **Extension**: a step that makes a language more expressive. It adds
  constructors, states, or predicates. Do not call it a refinement: a
  refinement is the predicate of a symbol (see Constraints). An extension is
  an abstraction extension or a definitional extension.
- **Abstraction extension**: an extension that tells more concrete tests
  apart, for example a new predicate in the vocabulary of the refinements. A
  term of the new version means a set of concrete tests: its
  **concretization**.
- **Definitional extension**: an extension that adds a named constructor for
  a pattern of the earlier version. A term of the new version means one term
  of the earlier version: its lowering.
- **Restriction**: a step that removes terms. It removes productions, adds
  facts, or adds named exclusions.
- **Lowering**: a translation of the terms of one language version to terms of
  the version before it. A **template lowering** gives each new constructor a
  template in the earlier version, and keeps each old constructor.
- **Language tower**: a language chain in which each abstraction extension
  has a concretization and each definitional extension has a lowering, so
  that each version has a meaning in L0.
- **Representation level**: one form of one language version: an editable
  definition, a graph, a prepared query, or a checkpoint. Do not call the
  levels a tower.
