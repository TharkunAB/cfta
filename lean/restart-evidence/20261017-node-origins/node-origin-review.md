# Bounded node-owner search

Updated: 2026-10-17 17:12 CEST. Baseline: e4b949a5. Source main: c0cc8a05.

The search found no active node-key recurrence in 3,651 constructed cases.
It made 30,669 instrumented outer requests. It found 11,788 returned hits.
At most eight owners were active at one time. Every result equalled the
result of current `reducePartially` by physical `Node` equality.

The finite family includes repeated raw guards at four finite levels,
productive plain recursive values, staggered operand guards, equal-length
and unequal-length paths, cross-copying, and the repaired historical cycle.
Every initial value is closed. The harness calls current
`reduceEdgeIntersection`, `combineEqConstraints`, `eqConstraintsDescend`,
`setChildren`, and `modifyNode`. The outer traversal and explicit active
and returned cells are copied instrumentation. They are not an extracted
worker or a verified host execution trace. Each instrumented traversal
starts with an empty outer table. The key uses actual `EqConstraints` Eq
and physical Node Eq. It does not compare path-class denotations.

Eight selected cases also passed in separate fresh processes. Each actual
`reducePartially` call starts with a fresh outer node memo. The preceding
instrumented traversal has already populated native and parent caches.
These checks do not establish an all-cache-empty host trace. The batch
also shares production memo tables between cases. The eight cases are a
subset of the 3,651 cases, not eight additional distinct cases.

Attempt 1 compiled but failed because the harness called partial
`nodeIdentity` on a valid empty result. Attempt 2 uses Node equality and
passed. This was a harness error, not a production counterexample.
Both attempts and their exact source snapshots remain in this directory.
The batch and selected checks used 4 GiB MemoryMax and MemoryHigh with
zero swap. All scopes are terminal. The successful batch peak was 663 MiB.

This is finite negative search evidence. It proves no general termination,
owner disjointness, rank, or source-to-Haskell correspondence theorem.
No Haskell defect was found. No production source was changed.

A possible next invariant must distinguish original occurrences even when
their raw guards agree. Plain wrappers above a constrained row can matter.
Native products can stack operand origins. Copies can occur deeper under
plain recursive values. A decreasing ghost-origin measure still needs a
physical same-key compatibility proof. None is established by this search.
