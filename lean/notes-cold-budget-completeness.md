# Exact general repaired cold tables and Sized classes

Updated: 2026-10-14 18:53 CEST.
Proofs: `a7b5d94e`, `9ca74b4d`, and `081ce3d1`.

## Raw plans refine to actual smart execution

`InternedGuardedSmartBudgetDeepSupport` and `DeepSyntax` use the existing
depth shapes. Each literal root language is included in the value language.
A change outside the deep names contributes only a literal root alternative.
The complete free-name support remains available as a separate field.

`InternedGuardedBudgetPlanRefinement` proves raw-to-smart inclusion for the
complete syntax. Retained Mu steps compare upward closed candidates. For an
unused smart binder, the smart body at the empty local is an upward closed
candidate for the raw Mu. The root/deep law handles root-only self alternatives.
`ValueRefinement` derives all shape and language premises from actual captured
records and upward ambient languages. No arbitrary shape-consistency contract
is assumed for the actual stored executor.

`InternedGuardedBudgetStoredRefinement.execute_refines` composes the exact raw
compiler and smart executor. `unfold_strict` proves that every accepted term
of an available Mu is accepted by its actual returned unfolding at a strictly
smaller budget. The result covers complete guards and arbitrary nested stored
plans. `constructed_unfold_strict` derives its heap and availability premises
from completed empty-cache construction. The actual successful unfolding is
explicit; existing completion theorems derive its existence.

## Actual cold-table completeness

`MergedFreshOrdinaryBudgetEffects` retains the new budget probe heap through
every bounded actual cold read. `SourceFreshOrdinaryColdBudgetHeap` retains it
through actual shared traces and finite traversal.

`MergedFreshOrdinaryExposureInputs` derives available closed values on every
epsilon path of an allocation-free completed read. Its traversal certificate
handles skipped visited identities. The direct Mu/node path uses actual replay
and cache growth. It does not assume that arbitrary future unfolding is cached.

`SourceFreshOrdinaryColdBudgetReachability` derives available closed epsilon
values from final replayed rows. Each constructor child starts a declared row.
`SourceFreshOrdinaryColdBudgetCompleteness.reached_complete` uses the ordered
measure `(term size, unfolding budget, stored value size)`. Constructor children
decrease term size. Mu steps decrease budget. Union alternatives decrease value
size. Thus each accepted budget gives a finite run in the actual repaired graph.

`SourceFreshOrdinaryColdGuardedExact.graph_exact` combines this result with the
existing soundness. Closed coherent available records derive `Original` syntax.
The existing exact input derivations supply the finite budget for every term
in independent guarded meaning. `trace_table_exact` identifies the actual finite
ascending table with that independent root language. `trace_table_input_exact`
also identifies it with the actual tagged input language in the initial cache.
No execution, copy-language, or graph-completeness contract is supplied.

## Sized and native composition

`SourceFreshOrdinaryColdSized.source_sized` covers general completed repaired
closed construction. It supplies an actual finite cold trace and stable bounds,
exact distinct node-count classes, finite execution for every class, complete
size-ordered prefixes, and both rank/unrank inverse laws. No preparation or
supplied cold trace is required. This composes the existing reference Sized
theorems; it does not change their canonical sequence or public query behavior.

`SourceRecursiveIntersectionBudgetEffects` proves budget-heap preservation for
actual optional binders. `Bounds.budget_heaps` follows complete actual native
evaluation, including ordinary work, nested calls, memos, and completion frames.
`cold_node_table_exact` supplies the exact independent language of the returned
native value. `constructed_node_table_exact` derives initial probe heaps from
completed closed source construction. Complete caches, closed Original operands,
actual effects, and checked `WordRanges` retain their existing scope.

## Next obligation and boundaries

The ordinary physical membership and rejection cases are now proved by
`2e6fb87a`, `6afdfe00`, and `dac5f26b`. A live ranked Mu witness refutes a
single public closed child map for general returned rows. Preserve the
existing functional theorem in its stated scope. Derive related physical
rows from actual domains, Mu reconstruction, union normalization, and child
traces. Then prove complete native two-input language and the minimum callback.
Read [ordinary product rows](notes-ordinary-product-rows.md) for the witness,
completed local laws, and current next target. Do not assume a product-language
contract or infer a runtime defect from different physical identities alone.

The primary reference, solver-decided, and optimized Sized source contracts
remain proved at their recorded boundaries. External solver correctness and
completion, concrete Haskell containers, lazy scheduling, and verified extraction
remain separate. Literal raw-binder reconstruction identity remains refuted.
Keep the optimized interned core, all repairs, counterexamples, and marked drafts.

## Validation

Pinned Lean 4.34.1 passes all focused checks and the aggregate audit:
1,456 jobs and 43,803 theorem dependency checks. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-cold-budget-exact-20261014-audit.log`.
All completed modules are imported by `MicroCFTA/Audit.lean`.
No production Haskell code changed. Prior Nix and formatter evidence applies.
All work remains local. No worker is active.
