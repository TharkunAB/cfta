# Memo reuse under binder registration

`MicroCFTA/PruneDependencies.lean` identifies the exact graph dependencies of
one finite-plan specialization. `reads` follows every row access through the
same edge and child-plan traversal as the specialization worker. It ignores
unobserved children, which remain shared references.

`specialize_rows_congr` proves exact result equality when these actual rows
stay equal. The graph can change elsewhere. `memo_rows_congr` transports the
whole memo invariant by applying that theorem to each stored query.

The source binder registry maps a recursive identity to its immutable node.
`register_wellKeyed` preserves that relation. `register_retains` proves that
registration cannot replace an earlier resolved node if node identity is
injective. `graph` models the source `alternatives` cases for an ordinary node
and a recursive reference, including the empty result for a missing binder.

`memo_register` proves that growing this registry preserves every stored
specialization when each previously queried recursive reference was already
registered. This is the precise remaining caller condition. The theorem does
not require the whole graph to remain syntactically equal.

`unresolved_rows_change` checks why the condition is necessary: an unresolved
reference has no alternatives, but later registration can give it a leaf.
This is a boundary example, not a reported source defect. Source validation,
binder insertion before body pruning, and `readsThroughRecursion` must ensure
that specialization never caches such an unresolved query. The complete
Haskell call-graph proof of that condition remains open. The node-identity
injectivity premise is the immutable interning contract, not a theorem about
the source allocator.

Validation: `lake build MicroCFTA.PruneDependencies` succeeds with the pinned
toolchain. It imports the complete memo worker and contains no proof holes.
