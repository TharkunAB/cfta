# Free-name semantics for the repaired constructor

`InternedFreshOrdinaryFreeNames.build_free` proves the free names of every
completed repaired expression from the independent pure syntax interpreter.
The ordered child and edge theorems retain the same source execution order.
They use the repaired root-profile heap and the repaired normalization facts.
No invariant for the old ordinary probe choice is assumed.

`InternedFreshOrdinaryFreeHeap.Correct` decodes complete Mu free names from
both actual stored probes, removing `Depth` from its own probe and
`U (ordinaryLevel depth)` from the ordinary probe. Distinct probe names
recover every capture, including a capture that equals either sentinel.
The actual request proof covers complete hits, fresh misses, and pending
outcomes. A pending outcome retains the invariant for completed records.
`closed_heap` derives the new invariant from empty caches.

`InternedFreshOrdinarySourceFreeNames.closed_free_empty` proves that every
completed closed expression has no free names. Its actual callback theorem
recovers the syntax-derived capture set away from the supplied argument.
`ordinary_above_captures` uses the completed Depth callback to show that the
selected level exceeds every ordinary capture of that callback's result.
`ordinary_from_captures` identifies its exact free-name bound with the pure
syntax-derived bound. These results include arbitrary nested constructors.
They do not assert that all intermediate discarded computations omit the
same names. That separate issue remains in the general completion proof.

`InternedFreshOrdinaryChooser.fold_exact` matches the source right fold.
`set_fold_exact` needs only equality of ordinary-reference membership.
Iteration order, duplicate names, and other reference kinds cannot change
the result. This gives the finite set representation boundary explicitly.
`word_set_fold_exact` also models the signed machine increment and maximum.
One bound on the selected mathematical result proves every intermediate
increment exact. For a 64-bit signed source Int, instantiate `bits` with 63.
This theorem does not establish that all runtime executions stay in range.

The new proofs preserve all old executor modules and counterexamples.
General repaired completion, complete accepted-language interpretation,
substitution at arbitrary matcher arguments, and unrestricted runtime
correspondence remain separate obligations.
