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
- **Counterexample** (inclusion): a term that the left automaton accepts and
  the right automaton rejects.
- **Partition**: a list of automata, the **parts**, that together accept each
  term of one automaton, the **whole**, and of which no two accept one term
  of the whole. The **part index** is the position of a part in the list. Do
  not call the parts children or the whole a parent: a child is a subterm or
  a child state, and a parent is a state or a union-find element.
- **Gap**: a term of the whole that no part accepts.
- **Overlap**: a term of the whole that two parts accept, with the indexes of
  the two parts. A term of two parts that the whole rejects is not an
  overlap.
- **Edit** (of a term): a change at one position of a term that keeps the
  state of the position. A **replacement** gives the position another term of
  its state. A **wrap** puts a new node of that state above the old subterm,
  as one of its children. A **context wrap** puts a new term with one hole
  above the old subterm: the old subterm fills the hole, and the hole is
  deeper than the children of the new root. An **unwrap** gives the position
  a child of its old subterm, when the state accepts that child. An **edit
  site** is a position with a kind of edit: a replacement, a wrap or a
  context wrap with a transition index and a child index, or an unwrap with a
  child index. The **new material** of an edit is what it adds: the new
  subterm, the other children of the new node, or the nodes of the new term
  of a context wrap. An unwrap has none. Not a row edit of an automaton
  (`Data.CFTA.replaceRows`). A **branching site** is an edit site below a
  state with two transitions for the symbol of the term there: with
  constraints, another transition can accept an edited term.
- **Edit set** (of a term): the edits at one to k sites of a term at pairwise
  incomparable paths, so that no edit is inside another. `Data.CFTA.Edit.Sets`
  gives the automaton of the edit sets. Its size is the number of the edits plus
  the total new material.
- **Edit tree** (of a term): an edit set where an edit may lie inside a wrap.
  A wrap or a context wrap holds edits only when the state of its hole is the
  state of its position (it is **treeable**). The edits inside change the old
  subterm before the wrap goes around it. `Data.CFTA.Edit.Trees` gives the
  automaton of the edit trees. Its size is the number of the edits plus the
  total new material, as for an edit set.
- **Linearization**: the texts around the children of each symbol, which give
  the text of a term: the first text, the text of the first child, the second
  text, and so on. A lowering gives a term; a linearization gives a text. Do
  not call the texts of a symbol a template: a template belongs to a template
  lowering. A *linearization by state* gives the texts by the state and the
  symbol of a transition, so the text of a term depends on its run.
- **Brackets**: an opening and a closing text around the text of a state: the
  state itself, or another state whose terms then count as terms of the
  state. The text in brackets has the term of the text inside, so a term with
  brackets has more than one text.

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
- **Measure**: the logical value of each term of a constructor, written as a
  term of the measures of its children (`measured`). The refinement of a constructed
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

- **Solver lowering**: a meaning-preserving translation of a logical
  obligation to a solver's supported representation. It can be partial.

- **Predicate definition**: a global predicate name with parameters and a
  body in the formula language. **Unfolding** replaces each application by
  the body, with the arguments in place of the parameters. It is a solver
  lowering for a solver without predicates.

- **Ground evaluation**: a decision of an entailment by computation. A
  **ground value** is an integer, or a data constructor applied to ground
  values. The equalities of the antecedent give names ground values, and
  fixed interpretations give the meanings of named functions and predicates.
  A query whose result needs a name without a value stays undecided.

- **Theory**: datatypes and definitions of functions and predicates in the
  formula language, in an order. Every solver reads the meanings of the names
  from the same theory.

- **Datatype**: a named sort and its constructors. Each constructor has typed
  fields. The constructors are free: two values are equal only when they have
  the same constructor and equal fields.

- **Case split**: a body with one branch for each constructor of the datatype
  of a parameter or a field. A branch binds the fields of its constructor.

- **Structural recursion**: a definition calls itself only with a field that
  a case split of one fixed parameter binds, directly or through case splits
  of its fields. Each call gets a smaller value, so the evaluation stops.

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
  The weight of a term is the product of the weights of the symbols of its
  nodes (`withWeights`).
- **Checked rank**: a rank of a term with whether the ranking checked every
  symbol of the term.
- **Occurrence**: the token of one recursion probe.

## Prefixes

- **Token**: one node of a term in preorder: its symbol and its number of
  children. Not the token of an occurrence.
- **Prefix**: the first tokens of the preorder of a term
  (`preorderPrefix`, `excludePrefixesFTA`). A *child prefix* of a count
  table, the first children of a transition, is a different thing.
- **Pending state**: the state of a subterm that a prefix does not reach.
  Each run of an automaton on the nodes of a prefix gives a stack of pending
  states, in preorder.
- **Completion**: an accepted term within a size bound whose preorder starts
  with a prefix.
- **Undecided completion, undecided token**: with a solver, a completion is
  undecided when the solver neither accepts nor rejects it. A token is
  undecided when the solver accepts none of its completions and some of them
  are undecided. An undecided token is neither offered nor rejected.

## Generators

- **Choice index**: the position of an alternative in a generator choice.
- **Component index**: which component of an n-way join.
- **Argument index**: the position of an argument of a join, a guard, or a
  contract.
- **Group index**: which matched key pair of a two-way join.
- **Key index**: the position of a key among the keys of a recursive family.

## Traces

- **State machine**: an initial state, a list of steps, the next state of a
  step in a state, and the final states (`StateMachine`). The
  **precondition** of a step is true in a state when the step has a next
  state there. The next state is the **postcondition** of the step.
  quickcheck-state-machine calls the next state the *transition*, and its
  postcondition checks a response. Do not call the next state a transition:
  a transition is a rule of an automaton. A **final state** is a state in
  which a trace can end.
- **Step**: one action of a state machine. When the next state depends on a
  response, the response is part of the step.
- **Guarded state machine**: a state machine whose state is named integers
  (`GuardedMachine`). A step can have an integer **parameter** from a range.
  Its **guard** is its precondition as a formula over the state and the
  parameter, and its **update** gives the new values of some names. In the
  refinement generator, the guard is the contract of the constructor of the
  step, and each name is a named measure of a prefix.
- **Trace**: a sequence of steps that a state machine accepts. In
  `Data.CFTA.Trace`, its term is the right spine
  `Step s1 (Step s2 (... (Step sn End)))`, so a trace of `n` steps has size
  `n + 1`, and a prefix of a trace is a preorder prefix of its term. In the
  generator of a guarded state machine, the last step is at the root, because
  a measure is calculated from the children. Do not call a trace a path: a
  path is a list of child indexes.

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
- **Variant**: a production of the later version of an abstraction extension
  that keeps the symbol text, the child states, and the constraint of a
  production of the earlier version, with another refinement. The variants of
  a production cover it when together they keep all its values.
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
