# First completion after computed empty children

`InternedComputedEmpty.EmptyResult` derives empty output from source
normalization. A node has a declared empty child on every requested edge.
A union has empty operands. The other children can contain arbitrary nested
constructors. `build_empty` uses their actual completed trace. It does not
assume that the source subtree completes.

`InternedComputedErasure.dead_residual` handles a dependent edge whose
blocking child computes EmptyNode. The blocking child has a structural
erasure certificate for the changed slot. The theorem derives its later
ordinary effects, executes the changed edge request, and reuses the earlier
surviving parent. It retains allocations made before the edge disappears.

`InternedComputedBinderReplay` connects this body result to the actual two
normalized probes and canonical Mu lookup. `Erases` permits either the
existing structural certificate or the computed-child form. The binder
replay proof derives the repeated request from the actual earlier probes.
It does not assume a stable callback key.

`InternedComputedCompletion.closed_completes` derives the first complete
execution by source induction. Every nested binder has an `Erases 1` body
and recursively admitted children. The proof constructs ordinary residual
work while the enclosing fresh reservation remains pending.
`closed_complete_record` also derives complete coverage, record provenance,
result availability, and replay after later cache growth.

`InternedComputedCompletionExamples.tower_complete` and
`tower_not_pending` cover arbitrary finite depths in both raw and smart
modes. Each blocking child evaluates a deeper nested binder, then a node
and a union normalize to empty. The outer-dependent edge is then removed.
The whole program has proved closed lexical scope.

The focused build has 165 jobs. The isolated audit checks 7,298 theorem
dependencies with only `propext`, `Classical.choice`, and `Quot.sound`.
A separate temporary Haskell probe passes all 16 raw and smart cases at
nested child counts zero through seven. It checks closure, exact cached
binder depth, and repeated canonical identity.

The empty witness has no Mu-root rule. In particular, these results do not
prove that arbitrary smart Mu cleanup returns empty from empty probe
metadata. Full source-call correspondence for arbitrary changed outer
inputs and general first-run completion remain open. The finite Haskell
probe is separate evidence; no automatic source translation is claimed.
