# 10. The e-graph is an ECTA with a union-find

## Context

ECTAs generalize e-graphs as representations of sets of terms: the language
of an e-class is the language of a state of a bottom-up deterministic tree
automaton, and an ECTA adds equality constraints to the transitions. Suciu,
Wang and Zhang (ICDT 2025) take this as the definition: an e-graph is a
deterministic and reachable tree automaton, and rebuilding is its congruence
closure. The e-graph of ADR 9 used this only at its edges. It kept its own
union-find and its own sets of e-nodes, and built an automaton from them to
count terms or to match by intersection. cfta already has the parts of an
e-graph that an automaton does not have: the explicit ECTA,
`FTA state symbol Constraint`, has nominal states and a constraint on each
transition, and the enumeration of an ECTA has a union-find for its
equalities.

## Decision

The store of `Data.CFTA.EGraph` is the transition table of an explicit ECTA.
Each root e-class is a state, and its e-nodes are the transitions of the
state; the sort of an e-node is the sort of its state. Merges use the
union-find of the ECTA enumeration, `Data.CFTA.Internal.UnionFind`.
`rebuild` restores the determinism of the automaton, which is the
congruence, and leaves a valid automaton, so `classAutomaton` is the
automaton with the rows that a state reaches. An e-node can have an equality
constraint on its transition (`addConstrained`). A constraint restricts the
terms of an e-class, not its equalities: the hash-cons, the users and the
matcher see the plain form of an e-node, and an e-node with a constraint is
in the e-class of its plain form.

## Why

- The claim of the module, that an e-graph is an ECTA, is then true of its
  data, not of a conversion.
- The interned ECTAs of cfta (`Data.CFTA.Interned`) are the wrong host. Their
  identity is structural: a merge changes the content of a node, so it
  changes the identity of the node and of each ancestor, and a cycle needs a
  binder. The explicit form has nominal states, which a union-find can merge.
- The terms of an e-class are equal to each other, so a constraint between
  the children of an e-node cannot make two e-classes equal or unequal. It
  can only remove terms from the language. So equality saturation ignores
  constraints, and extraction, counting and enumeration respect them.

## Consequences

- The e-graphs are the same: the AC sums, hegg's math rules at each
  iteration, and the output of HugeLists 5-p4 `--egraph extra`. Against the
  e-graph of ADR 9, in cachegrind instructions: +0.2 % on the AC sum of 9
  variables, and −10.1 % (t3) and +0.8 % (t4) on hegg's math rules after 6
  iterations; 5-p4 `--egraph extra` allocates 0.1 % more. At 6-p4
  `--egraph extra`, the laws and the proofs are the same, and the store
  allocates 1.3 % less. The first version of the store cost +29 % to
  +68 %. These changes brought the cost back:
  - The union-find of cfta points each member of the smaller set at the new
    representative on a union, so `root` is one lookup. The representative
    holds the size of its set and the set, an `IntSet` of the ids of the
    members. `unionRoots` merges two representatives and gives the new one,
    so a merge looks up each entry once.
  - Each e-class record holds its row, so the map of the e-classes is the
    table, and a merge or a new e-node changes one map. A transition has
    the symbol of its e-node, and the sort is the sort of the state.
  - Repair compares the children of a user with their roots, and makes a
    new e-node only for a user whose form changes (−4.4 % on t4).
  - A merge copies the shorter list of users and the row of the smaller
    set. Against a copy of the shorter row, found by a walk of the lengths,
    this is −3.0 % on AC and +1.8 % on t4; the difference is in the
    garbage collector (`evacuate`).
  - The matcher reads the rows of the store, so the snapshot of an
    iteration without a goal is the table itself, and it compares the
    identities of two roots for a variable that occurs twice.
  - Rebuild tidies only the rows that can have a child that is not a root
    or a transition twice: the rows of the merged e-classes and of the users
    whose form changed, in one merge of the e-classes with those roots.
  - The matcher matches the children of arities 0 to 2 without a walk of
    the lengths. This change costs +1.2 % of allocation on 5-p4 and saves
    2.1 % of instructions on AC and 2.3 % on t4.
- What stays of the cost is mostly in `union`: the union-find of cfta keeps
  the size and the members of a set in the entry of its representative, so
  a union inserts that entry and looks up two entries, which a map of
  parents alone does not.
- `classAutomaton` gives the rows of the table that the state of an e-class
  reaches as an `FTA`.
- The e-nodes of the hash-cons and of the users stay compact: an e-node with
  at most two children keeps them unboxed.
- An e-node whose constraint no term satisfies leaves its e-class without
  terms when it is the only e-node of the e-class.
- Two other forms of the union-find are not in the history: a separate map
  of the members of each set (+9 % on AC), and a list of the members in
  place of the set (against the set: +1.0 % on AC, +1.1 % on t3, −0.9 % on
  t4, and the same standard cells). A union points each member of the
  smaller set at the new root, so it walks the members in each form. The
  set is the notion of the scheme, so it stays.

## Discussion points

- The other direction, cfta operations on the e-graph engine (determinizing
  or minimizing an FTA with the union-find and the hash-cons), stays open.
- Speed against hegg is not the aim of this change; the cost above is the
  start for that work.
- The union-find is the linked-list representation of disjoint sets with
  the weighted-union heuristic (Cormen et al., Introduction to Algorithms):
  each member points at the representative, and a union relabels the
  smaller set. So a lookup of a representative is one step, and n unions
  relabel O(n log n) members in all.
- egg makes the e-nodes of every e-class canonical and removes duplicates
  in each rebuild. This rebuild touches only the rows that can change.
- Relational e-matching (Zhang et al., POPL 2022) reads the e-nodes of each
  symbol as a relation and answers a pattern as a conjunctive query with a
  worst-case optimal join. The rows of the store, by symbol, are those
  relations. The matcher here is a backtracking search down the pattern, as
  egg's is, and it starts at the e-classes of the rarest symbol.
