# Redundant alternatives and cyclic rewrites

`RedundantEdges` follows `dropRedundantEdges.reduceCluster` and `ruleOut`.
It includes the source optimization that moves a dominating alternative to
the front of the next comparison. `ruleOut_length` proves strict progress for
both recursive reduction branches. The Lean reduction terminates without fuel.

`ruleOut_exact` and `reduce_exact` preserve the union of accepted terms under
the edge-intersection contract. Equality of interned edge identities then
justifies each removal. `clusters_exact` and `grouped_exact` preserve the
combined language after key grouping. Hash collisions must not merge unequal
symbol keys; this is the source hash-map lookup contract. Cluster order does
not affect the language.

The intersection theorem is stated for an edge domain where intersection is
total. For one source cluster this is the fixed-symbol edge domain. Across
clusters, a total extension maps unequal-symbol intersections to an empty
edge. The source never compares these cross-cluster pairs.

`GraphRewrite.rows_preserve_language` proves the whole-graph step. If each new
row has exactly its old meaning under the original child-state languages,
then every complete finite term has the same acceptance in both graphs.
The proof uses structural induction on the term. It applies to cyclic graphs
because each transition consumes one constructor. `reduce_graph_exact`
instantiates the result for interned edge identities and the checked reduction.
It does not replace finite acceptance by a coinductive language.

The source's recursive binder rebuilding and its mapping between old and new
identities still require a concrete representation correspondence. The local
comparison loop, its termination, and the global constructor-graph consequence
are checked separately from that adapter.
