# 10. The e-graph is an ECTA with a union-find

## Context

ECTAs generalize e-graphs as representations of sets of terms: the language
of an e-class is the language of a state of a bottom-up deterministic tree
automaton, and an ECTA adds equality constraints to the transitions. The
e-graph of ADR 9 used this only at its edges. It kept its own union-find and
its own sets of e-nodes, and built an automaton from them to count terms or
to match by intersection. cfta already has the parts of an e-graph that an
automaton does not have: the explicit ECTA, `FTA state symbol Constraint`,
has nominal states and a constraint on each transition, and the enumeration
of an ECTA has a union-find for its equalities.

## Decision

The store of `Data.CFTA.EGraph` is the transition table of an explicit ECTA.
Each root e-class is a state, and its e-nodes are the transitions of the
state, with the sort in the symbol. Merges use the union-find of the ECTA
enumeration, `Data.CFTA.Internal.UnionFind`. `rebuild` restores the
determinism of the automaton, which is the congruence, and leaves a valid
automaton, so `classAutomaton` is the automaton with the rows that a state
reaches. An
e-node can have an equality constraint on its transition (`addConstrained`).
A constraint restricts the terms of an e-class, not its equalities: the
hash-cons, the users and the matcher see the plain form of an e-node, and an
e-node with a constraint is in the e-class of its plain form.

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
  e-graph of ADR 9, in cachegrind instructions: +2.1 % on the AC sum of 9
  variables, and −4.5 % (t3) and +4.9 % (t4) on hegg's math rules after 6
  iterations; 5-p4 `--egraph extra` allocates 0.1 % more. The first version
  of the store cost +29 % to +68 %. These changes brought the cost back:
  - The union-find of cfta points each member of the smaller set at the new
    representative on a union, so `root` is one lookup.
  - Each e-class record holds its row, so the map of the e-classes is the
    table, and a merge or a new e-node changes one map.
  - A merge copies the shorter of the two lists of users and of the two
    rows.
  - The matcher reads the rows of the store, so the snapshot of an
    iteration without a goal is the table itself.
  - Rebuild tidies only the rows that can have a child that is not a root
    or a transition twice: the rows of the merged e-classes and of the users
    whose form changed.
  - The matcher matches the children of arities 0 to 2 without a walk of
    the lengths. This change costs +1.2 % of allocation on 5-p4 and saves
    2.1 % of instructions on AC and 2.3 % on t4.
- `classAutomaton` gives the rows of the table that the state of an e-class
  reaches as an `FTA`.
- The e-nodes of the hash-cons and of the users stay compact: an e-node with
  at most two children keeps them unboxed.
- An e-node whose constraint no term satisfies leaves its e-class without
  terms when it is the only e-node of the e-class.
- Two other union-finds are not in the history: one with a separate map of
  the members of each set (+9 % on AC), and one with an `IntSet` of the
  members in place of the list (+1.0 % on AC and t3, −1.1 % on t4, the same
  on the standard cells). A union points each member of the smaller set at
  the new root, so it walks the members in each version.

## Discussion points

- The other direction, cfta operations on the e-graph engine (determinizing
  or minimizing an FTA with the union-find and the hash-cons), stays open.
- Speed against hegg is not the aim of this change; the cost above is the
  start for that work.
