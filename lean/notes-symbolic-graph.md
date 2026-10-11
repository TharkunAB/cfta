# Symbolic graph restriction and projection

`SymbolicGraph` supplies language proofs for the primitives used by
`Gen.Internal.Symbolic.selectAt` and `rankAt`.

Path conditioning has an explicit-state representation. The selected
constructor becomes an exact node template. Each earlier path step becomes
a prefix template with holes for all other children. `condition_root_step`
proves the source's symbol-and-arity filter. `condition_child_step` proves the
source's one-child update, missing-child rejection, and unchanged siblings.
The underlying `Template.restrict` proof preserves every original guard.
`condition_exact` gives both directions of accepted-language restriction.
It applies to cyclic graphs and complete finite terms.

`projectStates` follows the source's path/set worker. It collects rows, selects
existing child indices, removes duplicate states, and repeats for the suffix.
`projectRows` unions the final rows. `project_coverage` proves that every
existing subtree of an accepted term is accepted by these projected rows.
`rows_union_exact` proves that the row union represents exactly the combined
state languages. `project_root_exact` covers the empty path.

Projection at a nonempty path is an upper bound. It does not retain ancestor
constraints. The ranker needs coverage here, not exact existential projection.
The proofs do not impose the stronger false contract.

The explicit-state copy must correspond to the interned `condition` graph.
The checked recurrences identify its required rows, child order, and guards.
Concrete binder allocation, interning, and graph identity are still the
representation boundary. The distinct-count and selection proofs have their
own cache and termination obligations.
