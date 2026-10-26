# 10. The e-graph is an ECTA with a union-find

## Context

ECTAs generalize e-graphs as representations of sets of terms: the language
of an e-class is the language of a state of a bottom-up deterministic tree
automaton, and an ECTA adds equality constraints to the transitions. Suciu,
Wang and Zhang (ICDT 2025) take this as the definition: an e-graph is a
deterministic and reachable tree automaton, and rebuilding is its congruence
closure. A dedicated e-graph uses this only at its edges: it keeps its own
union-find and its own sets of e-nodes, and builds an automaton from them to
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

- Against a dedicated store with its own map of parents and its own sets of
  e-nodes, the e-graphs are the same, and the cost is about the same: in
  cachegrind instructions, +0.2 % on the AC sum of 9 variables, and −10.1 %
  (t3) and +0.8 % (t4) on hegg's math rules after 6 iterations. With 4,000
  e-nodes and no backoff, HugeLists `--egraph extra` allocates 0.1 % more at
  5-p4 and 1.3 % less at 6-p4, with the same laws and proofs.
- The cost rests on these parts of the design:
  - The union-find is the linked-list representation of disjoint sets with
    the weighted-union heuristic (Cormen et al., Introduction to
    Algorithms): each member points at its representative, and the
    representative holds the size of its set and the set as an `IntSet`.
    So `root` is one lookup, and n unions point O(n log n) members in all.
    `unionRoots` merges two representatives and gives the new one.
  - Each e-class record holds its row, so the map of the e-classes is the
    transition table. A transition has the symbol of its e-node, and the
    sort is the sort of its state.
  - Rebuild makes canonical only the rows that can change: the rows of the
    merged e-classes, and of the e-classes of the users whose children
    changed.
  - The matcher reads the rows, so the snapshot of an iteration without a
    goal is the table itself.
- Most of what stays of the cost is in `union`: the entry of a
  representative holds the size and the set, so a union writes that entry,
  which a map of parents alone does not.
- The ECTA enumeration shares the union-find: on the standard cells, it is
  within 0.05 % of instructions, and `enumeration-speed 1` is +0.44 %, with
  the same checksums.
- `classAutomaton` gives the rows of the table that the state of an e-class
  reaches as an `FTA`.
- The e-nodes of the hash-cons and of the users stay compact: an e-node with
  at most two children keeps them unboxed.
- An e-node whose constraint no term satisfies leaves its e-class without
  terms when it is the only e-node of the e-class.

## Discussion points

- The other direction, cfta operations on the e-graph engine (determinizing
  or minimizing an FTA with the union-find and the hash-cons), stays open.
- Speed against hegg is not the aim of this decision.
- A list of the members in place of the `IntSet` costs about the same
  (+1.0 % on AC, +1.1 % on t3, −0.9 % on t4); the set is the notion of the
  scheme. A separate map of the members of each set costs +9 % on AC.
- egg makes the e-nodes of every e-class canonical and removes duplicates
  in each rebuild. This rebuild touches only the rows that can change.
- Relational e-matching (Zhang et al., POPL 2022) reads the e-nodes of each
  symbol as a relation and answers a pattern as a conjunctive query with a
  worst-case optimal join. The rows of the store, by symbol, are those
  relations. The matcher here is a backtracking search down the pattern, as
  egg's is, and it starts at the e-classes of the rarest symbol.
