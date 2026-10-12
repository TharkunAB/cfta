# First-run completion through recursively erased dependencies

`InternedNestedErasureReplay` removes the finite ordinary-body restriction
from the earlier erased-edge replay theorem. The live edge list can contain
arbitrary nested source binders. Its original lexical input slots exclude
slot one, which holds the changed outer value. The appended dead edge reads
that slot and an empty child.

`callback_residual` extracts the live-child computation from the actual
earlier successful callback. Syntax-derived input agreement and whole-source
replay reproduce those complete children. The callback then executes the
changed discarded-edge request. Node normalization removes that edge and
reads the earlier complete parent. `binder_residual` composes both real
probes and reads the earlier complete Mu record. Its residual work retains
both discarded-edge requests. It does not assume a callback key equation.

`InternedNestedCoherence` supplies the state-field proof needed for these
arbitrary earlier source traces. It covers both completed and pending
outcomes without assuming complete input payloads.

`InternedRecursiveErasure.Admitted` applies the erased-edge declaration at
every nested binder. Live children can contain further admitted binders.
Ordinary node and union child positions remain unrestricted. The live
children can read the local inner variable and older captures; they must
exclude the changed immediate outer slot. Each inner body ends with its
declared outer-dependent edge that contains an empty child.

`build_residual`, `buildMany_residual`, and `buildEdges_residual` derive a
complete first execution and safe ordinary residual work by source syntax
induction. The binder case first derives its complete depth-body execution
recursively. `binder_from_residual` executes the later callbacks while the
new outer Mu is pending. The derived replay theorem then supplies the
residual for later changed enclosing values.

`closed_completes` and `closed_complete_record` start from empty caches.
They assume the stated source grammar and no successful first run, stable
key law, or global family law. The result has complete record coverage,
full availability, and exact subsequent whole-program replay.

`InternedRecursiveErasureExamples` proves a closed, scoped tower at every
finite depth, for both raw and smart Mu construction. All edges use symbol
zero. Each nested call syntactically reads its immediate outer slot.
`tower_inputs` proves that fact. `tower_not_pending` excludes an unfinished
readback for every tower depth.

A temporary Haskell probe also exercised the live `Data.CFTA.Interned`
constructors under the project Nix environment. All 14 raw and smart
towers with zero through six inner layers completed. Each had an empty
free-variable set, exact cached depth, and canonical equality on repeat
construction. The probe and its output are in
`/tmp/mcfta-recursive-erasure.hs` and `/tmp/mcfta-recursive-erasure.log`.
This executable evidence is separate from the unbounded Lean theorem.

This closes arbitrary recursive nesting of the declared empty-child edge
erasure. General mixed retention and erasure remains open when live source
children read the changed outer slot and later normalize away that use.
Union-induced erasure and binder-cleanup erasure also need source-call
correspondence. These statements do not prove completion for every closed
source expression.
