# Source-call correspondence for erasure below nested constructors

`InternedErasureSyntax.Erased` tracks one changed lexical input slot.
Its base erasure rule is an actual source node with an appended edge that
reads that slot and an empty child. The relation composes through arbitrary
node children, union members, and raw or smart Mu bodies. Crossing a binder
increments the tracked slot. A subexpression that omits the slot can use
arbitrary source syntax.

`InternedErasureCorrespondence.build_erased` derives source-call
correspondence from this declaration and the earlier actual complete trace.
It permits the changed read inside live children and below nested binders.
The result is safe ordinary residual work that returns the exact earlier
value. The residual retains all changed discarded-edge effects in source
order. The Mu case derives both earlier probes and reads the earlier
completed request. It does not assume a callback key-stability law.

`InternedErasureResidual` composes these exact earlier results and later
ordinary effects. `InternedErasureChildren` derives their ordered child
and edge composition from the actual source execution.

`InternedDeepErasureCompletion.Admitted` requires each nested binder's
body to erase its immediate outer slot and recursively admit its nested
constructors. Bodies can start with nodes, unions, or further binders.
`build_residual` derives the first complete body execution by syntax
induction. It then applies the normalized correspondence theorem to derive
the later callbacks. `closed_completes` and `closed_complete_record` start
from empty caches. They have no earlier-success, stable-key, or whole-family
completion premise.

`InternedDeepErasureExamples` gives a closed, scoped family at every finite
depth. Each layer reads both parent and grandparent names inside live child
nodes. Each layer also has a root self union. All edges use one symbol.
`tower_reads_grandparent` proves the original lexical read.
`outside_previous` proves that the earlier root-node erasure grammar does
not admit these inner calls. `tower_complete` and `tower_not_pending` prove
first completion and exclude pending readback for every raw or smart depth.

A temporary Haskell probe exercised the live `Data.CFTA.Interned`
constructors under Nix. All 12 raw and smart cases with zero through five
inner layers completed. Each had an empty free-variable set, exact cached
depth, and canonical equality on repeat construction. The files are
`/tmp/mcfta-deep-erasure.hs` and `/tmp/mcfta-deep-erasure.log`. This finite
source evidence is separate from the unbounded Lean theorem.

The general first-run theorem for every closed source expression remains
open. The structural declaration still needs an explicit empty-child edge
or an unused input at its base. It does not infer erasure from final cached
free metadata, union identity collapse, or smart Mu cleanup. General mixed
retention and erasure also needs one proof that combines the active pending
contexts. No theorem here replaces those obligations with an assumed law.
