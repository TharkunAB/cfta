# 9. cfta has a sorted e-graph, and Specftacular uses it

## Context

An e-graph is a bottom-up deterministic tree automaton, and an ECTA
generalizes it, so cfta can give e-graphs to any language of terms.
Specftacular can then decide with equality saturation whether its printed
laws prove a new law, and it is the benchmark of the e-graph. Its terms are
typed: the constant `[]` at two types is two e-nodes, the right side of a
law needs its type variables, a side that is a bare variable needs the type
of its e-class, and types never merge. Other languages need what egg and
hegg give: analyses such as constant folding, and conditional rules.

## Decision

`Data.CFTA.EGraph` is a sorted e-graph, as in egglog. Each e-class has a
sort or no sort; a sort is a hash-consed term that never merges and is part
of the identity of an e-node. A pattern can give a variable or a node a sort
pattern with sort variables.

The matcher goes down from each root with one substitution, as in egg. A
rule takes its roots from the symbol of its left side with the fewest
e-classes, up through the users of each e-class. Each e-class has the stamp
of its last change, and a rule finds only the matches through e-classes
newer than its last run (semi-naive, as in egglog); when few e-classes
changed, the roots come from the paths up from them.

`saturateWith` takes an e-class analysis and a condition for each rule. The
analysis is the fixed point of an evaluation of the e-graph automaton from
the leaves up (`analyse`), kept up to date from the e-classes that changed.
A leaf of the data, such as a constant, merges into its e-class.

`ematchByIntersection` keeps the definition of a match: the terms of the
product of the e-graph and pattern automata with the equality constraints of
the pattern. A property test checks that `ematch` gives the same matches.
Specftacular compiles its laws to rules of this module (`--egraph`, off by
default).

## Why

- An untyped e-graph with guards leaves the encoding of types to each user.
- With one symbol for each application, as in a curried encoding, the root
  symbol does not select roots; the rarest symbol does (226 GB against
  245 GB at HugeLists 5-p4 `--egraph extra`).
- Semi-naive matching skips the matches that the rule already applied: an
  AC sum of 9 variables allocates 24 % less, 10 variables 13 % less. At 5-p4,
  where each query saturates for a few iterations, it costs 0.4 %.
- On the same e-graphs, the engine allocates a quarter to a third of what
  hegg 0.6 does, and takes 31 % to 56 % of its time, on AC sums of 8 to 10
  variables saturated. On hegg's own math rules, which need conditions and
  constant folding, it builds the same e-graphs as hegg through iteration 3
  (t3) and 4 (t4), and it allocates less and takes less time at every size:
  0.50 to 0.63 s against 1.72 to 1.74 s for t4 after 6 iterations, where the
  two e-graphs are within 2 %. The analysis there
  propagates a change through the e-nodes that use the e-class, as egg does;
  recomputing the whole e-class takes three times as long.
- The matcher passes each match to a continuation. A list monad makes a
  list of the matches of each part of a pattern, and the AC sums allocate
  25 % more with it.
- The children of an e-node are evaluated roots, so that a key of the memo
  has no thunks.

## Consequences

- HugeLists 5-p4 `--egraph extra` prints 286 laws, against 291 off, and the
  e-graph proves 6.
- The e-node limit stops a saturation at a point that depends on the order
  of the matches, so a change of that order can change which laws the
  e-graph proves.
- Each Specftacular query has its own e-graph. One e-graph for all queries,
  with matching of all e-classes, gives 1 proof for 855 GB at 5-p4: each
  query matches the history that it reaches and uses its e-node limit on
  matches that earlier queries left.
- A condition sees the data when its match applies, as in egg and hegg. On
  hegg's math rules the two engines build different e-graphs after
  iteration 3 or 4. One cause is the merge of hegg's test analysis, in
  which an unknown constant absorbs a known one: hegg adds a constant leaf
  while the data of an e-class is a constant for a moment, and the fixed
  point here never has that data. With a merge in which the known constant
  wins, as in egg, the first difference of t1 goes away; the later ones are
  not explained.

## Discussion points

- A memo of the matches of each pair of an e-class and a pattern node lets
  parents share matches, but costs more than it saves: AC sum of 8
  variables, 887 MB against 842 MB top-down; 5-p4, 226.0 GB against 218.4 GB.
- hegg matches over its memo, so the e-nodes that its constant folding prunes
  from an e-class still match, and its pruning changes only its counts. This
  module does not prune.
- `merge` returns Nothing for two sorts, so that a mistake is not silent.
- The library limits follow egg (30 iterations, 10,000 e-nodes, a backoff
  from 1,000 matches); Specftacular uses 8, 4000, and no backoff.
