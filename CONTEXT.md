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
- **Graph snapshot**: a stored explicit graph with its symbols, refinements,
  constraints, states, and transitions. It need not retain the source facts
  from which its compiled constraints were made.

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

## Editable languages

- **Language**: a set of terms. A `Language` value is the source of one: a
  source document and named exclusions. Its terms are the terms of the
  compiled document that no exclusion rejects.
- **Source document**: an editable language definition that retains named
  productions and their separate facts before compilation.
- **Production**: a transition of a source document, with a name that is
  unique in its state, and named facts.
- **Language update**: a reusable expression that changes a source document or
  named exclusions. It does not contain an expected source version.
- **Named exclusion**: an exclusion with a name in a language. An update can
  remove it again. The source document does not change.
- **Production reference**: a source state and the stable name of one
  production in that state.
- **Source fact**: one named constraint attached to a production.
  Removing a fact removes that obligation. It does not negate the constraint.
- **Patch**: an ordered batch of edits together with the source document it
  expects. A valid patch produces a new source document.
- **Three-way merge**: the merge of two versions of a language, the left and
  the right, that come from one base. It merges by key: the initial state, the
  state rows, the production names, the fact names, and the exclusion names.
  A key that one side changes takes that change. A key that both sides change
  in the same way takes that change.
- **Conflict**: a key that the two sides of a three-way merge change in
  different ways, or that one side deletes and the other side changes. A
  conflict holds its key and its three versions.
- **Revision** (`Revision`): a language with its parents, its origin, and its
  metadata, in the store of `cfta-store`. Its **revision id** is the SHA-256 hash
  of the canonical text of the language, so equal languages have one revision
  id.

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
  The weight of a term is the product of the weights of the symbols of its
  nodes (`withWeights`).
- **Ticket**: one unit of a weight (the word of lottery scheduling,
  Waldspurger and Weihl). An alternative with the weight *w* holds *w*
  consecutive tickets, and a weighted selection draws one ticket uniformly.
  A **ticket table** gives the alternative that holds each ticket.
- **Checked rank**: a rank of a term with whether the ranking checked every
  symbol of the term.
- **Occurrence**: the identifier of one recursion probe.
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

## Prefixes

- **Token**: one node of a term in preorder: its symbol and its number of
  children.
- **Prefix**: the first tokens of the preorder of a term
  (`preorderPrefix`, `excludePrefixesFTA`). A *child prefix* of a count
  table, the first children of a transition, is a different thing.
- **Pending state**: the state of a subterm that a prefix does not reach.
- **Prefix run**: a run of an automaton on the nodes of a prefix: the stack
  of its pending states, in preorder, and the constraints of the prefix nodes
  that the prefix does not decide. Not a sampled run.
- **Completion**: an accepted term within a size bound whose preorder starts
  with a prefix. The completions of a prefix are in the order of
  `Data.CFTA.Sized`.
- **Candidate**: with a solver, a term of the automaton with each constraint
  reduced to its equality constraints. The solver accepts, rejects, or does
  not decide each candidate.
- **Offered token**: a token with an accepted completion (`nextTokens`).
- **Undecided completion, undecided token**: with a solver, a completion is
  undecided when the solver neither accepts nor rejects it. A token is
  undecided when the solver accepts none of its completions and some of them
  are undecided. An undecided token is neither offered nor rejected.
- **Refusal**: the reason that a token is not offered after a prefix. The
  token is rejected, the token is undecided, or the prefix is a whole term.
- **Walk**: a path of tokens with the verdicts of the solver kept for each
  step (`Deciding`). It asks the solver only when a query needs a verdict.
- **Mask**: the tokens that can come next after a prefix: the tokens of
  `nextTokens`. The record `Mask` (`Data.CFTA.Mask`) holds the mask of a
  prefix and the step after each token. `completionsMask` gives this record
  for each prefix of a `Completions` value.
- **Linearization**: the texts around the children of each symbol: the text
  before the first child, the text between each two children, and the text
  after the last child (`Data.CFTA.Mask.Text`). It gives the text of a term.
- **Reading**: a prefix of term tokens with a place in its text. The mask of
  a text prefix holds the readings of the prefix, and each reading has the
  items that are still to come: rests of texts and children.
- **Vocabulary, entry**: a list of entries, each a name with a list of tokens
  of a mask (`Data.CFTA.Mask.Vocabulary`). For a tokenizer, an entry is a
  short sequence of characters. The mask of the entries offers an entry when
  the mask below steps through each token of the entry. Not a token of the
  mask below, although machine learning calls an entry of a tokenizer a
  token.
- **Scorer**: a function from a prefix to the log-scores of the next tokens
  (`Data.CFTA.Guided`). Not a trained model of weights
  (`Data.CFTA.Sized.Prefix.Model`).
- **Guided search**: a search over the terms of a language whose steps a
  scorer scores, under the mask (`Data.CFTA.Guided`). Machine learning calls it
  constrained decoding; here, to decode is to unrank.
- **Weighing**: how a step of a guided search weighs the offered tokens before
  the normalization. It adds to the score of each offered token zero
  (`MaskOnly`), or the log of the probability of the token under the weights
  of the completions (`WeighCompletions`).
- **Visit**: one step of a guided search at a prefix that is not complete. The
  search reads the mask and the scores of the prefix, and keeps them with its
  choice (`Visit`). The trace of a search is the list of its visits.
- **Dead end**: a prefix of a guided search that is not complete and has no
  token with a finite step log-probability. The search takes the best open
  prefix.
- **Repair**: the continuation of a token sequence that a mask refuses. It
  keeps the longest prefix of the sequence whose tokens the masks offer, and
  searches from that prefix (`repair`).
- **Mask cache**: the masks of the prefixes that a guided search opened, by
  prefix (`MaskCache`). A later search on the same language reads them.
- **Text token**: a character of a text, or the end of the text
  (`Data.CFTA.Mask.Text.TextToken`). It is a token of the mask of a text. Not
  a **Token** of a term.
- **Event**: a set of terms, as in probability: the terms that an automaton
  accepts. A model given an event (`condition`) gives each term of the event
  its probability divided by the probability of the event. Not a diagnostic
  event of Specftacular.
- **Mixture**: a distribution over the completions that is a sum of
  distributions, each with a share. The probability of a term is the sum,
  over the mixture components, of the share times the probability of the
  term in the component (`Data.CFTA.Sized.Prefix.Mixture`). Not a *mode*: in
  statistics, the mode is the most probable value.
- **Mixture component, share**: one distribution of a mixture, and the
  probability that a term of the mixture is a term of this distribution. The
  shares of a mixture sum to one. The component of a term is hidden. Not the
  component of a join (**Component index**).

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
- **Language tower** (`Data.CFTA.Tower`): a base language L0 and a chain of
  checked extensions. Each version has a **step** to the version below. A
  definitional extension lowers new constructors through templates. An
  abstraction extension maps variants to the productions they came from.
  The **meaning** of a term in L0 is the result of applying each step in turn.
  A **preview** contains the language and edit for the next version. It can
  be committed to the tower it was checked against.
- **Representation level**: one form of one language version: an editable
  definition, a graph, a prepared query, or a checkpoint. Do not call the
  levels a tower.
