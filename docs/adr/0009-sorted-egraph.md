# 9. cfta has a sorted e-graph, and Specftacular uses it

## Context

An e-graph is a bottom-up deterministic tree automaton, and an ECTA
generalizes it, so cfta can give e-graphs to any language of terms.
Specftacular can then decide with equality saturation whether its printed
laws prove a new law, and it is the benchmark of the e-graph. Its terms are
typed: the constant `[]` at two types is two e-nodes, the right side of a
law needs its type variables, a side that is a bare variable needs the type
of its e-class, and types never merge.

## Decision

`Data.CFTA.EGraph` is a sorted e-graph, as in egglog. Each e-class has a
sort or no sort; a sort is a hash-consed term that never merges and is part
of the identity of an e-node. A pattern can give a variable or a node a sort
pattern with sort variables. The matcher goes down from each root with one
substitution, as in egg, and a rule takes its roots from the symbol of its
left side with the fewest e-classes, up through the users of each e-class.
`ematchByIntersection` keeps the definition: the terms of the product of the
e-graph and pattern automata with the equality constraints of the pattern. A
property test checks that the two give the same matches. Specftacular
compiles its laws to rules of this module (`--egraph`, off by default).

## Why

- An untyped e-graph with guards leaves the encoding of types to each user;
  Specftacular had its own engine for this reason.
- With one symbol for each application, as in a curried encoding, the root
  symbol does not select roots. The rarest symbol does: 244.7 GB to 226.0 GB
  of allocation at HugeLists 5-p4 `--egraph extra`.
- A memo of the matches of each pair of an e-class and a pattern node lets
  parents share matches, but it costs more than it saves. On an AC sum of 8
  variables it allocates 887 MB against 842 MB top-down, in 0.48 s against
  0.33 s to 0.41 s; at 5-p4, 226.0 GB against 218.4 GB.

## Consequences

- HugeLists 5-p4 `--egraph extra` prints the 286 laws of the earlier engine,
  proves the same 6, and allocates 218.4 GB against 211.3 GB (+3.4 %). Off
  allocates 176.8 GB, as before.
- The e-node limit stops a saturation at a point that depends on the order
  of the matches, so a change of that order can change which laws the
  e-graph proves.
- Each query has its own e-graph. One shared e-graph for all queries gave
  1 proof for 855 GB at 5-p4: each query matched the history that it reaches
  and used its e-node limit on matches that earlier queries left. Sharing
  needs matching of only the changed e-classes first.

## Discussion points

- In the earlier engine, reading the runs of the product instead of its
  terms (`FTA.terms`) made the matches by intersection 3 times faster. The
  module keeps the terms as the definition and the test oracle, where speed
  does not matter.
- `merge` returns Nothing for two sorts, so that a mistake is not silent.
- The library limits follow egg (30 iterations, 10,000 e-nodes, a backoff
  from 1,000 matches); Specftacular uses 8, 4000, and no backoff.
