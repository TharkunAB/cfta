# Actual allocated class entry into current conjunction Scan

Date: 2026-10-16 07:12 CEST.

The new source is `lean/MicroCFTA/SourceCurrentConjunctionAllocatedClassEntry.lean`.
The 132-line source is frozen at SHA256
`569ada204816c67d33cbbd87195e8ee45230219e0e3d185cdaefe8060f6877a5`.
No older source was edited for this task.

## Validation

- Pinned Lean 4.34.1 focused Lake build: terminal 0, 1277 jobs.
- Final raw log: `allocated-entry-build-final.log`.
- Only the existing unused `inputs` warning appeared in an older dependency.
- The initial log retains a repaired noncomputable declaration error.
  No proof repair was needed after the first elaboration.
- Standalone probes: terminal 0, no warnings.
- Four public declaration axiom probes and four signature checks passed.
- All probes use only `propext`, `Classical.choice`, and `Quot.sound`.
- Eight kernel examples passed. They check the complete returned operations,
  unchanged native state and heap, actual returned interner and operation
  tables, retained loaded fields, and retained scoped native cache.

## Derived entry

`prefixState` contains the literal operation state returned by
`SourceEqualityPartialPrecheckAllocation.run`. It retains the constructed
native state. It does not replace the returned operations with initial
operations or reset any completed equality-operation table. Positive empty
allocations therefore retain their actual represented identities.

`operations_ready` derives checked Good and current Scan.Ready from actual
operation Valid and Grows at the unchanged native heap. Existing field
availability grows by the same-cache load retention theorem. Native scope,
Idle, semantic readiness, stored costs, and both native tables are unchanged.

`entry` uses the same actual covered History, initial interner validity,
original construction, and resident edge as the prior original-entry proof.
It derives the original successful field load and ready stored constraint.
A ready inherited constraint and actual live prefix output derive operation
Valid/Grows and Scan.Ready at prefixState. The physical precheck receipt
derives proper selected paths and the exact equation
`output = ordered records`. The result also records the actual own accessor,
source class readback, coherent records, ascending tries, and nontrivial
original paths. This is exact list order, not only set membership.

`finite` fixes `SourceMemoGate.unconstrained` and its actual reaches predicate.
It derives edge.children availability from the resident edge. It invokes
only the NEW current conjunction ScanCompletion.finite at prefixState.
It returns an actual current Scan, final Ready, physical Effects from the
actual post-prefix state, retained child availability, fourth-memo Correct,
and fourth-memo Extends.

## Explicit boundaries

The endpoint retains actual causal allocation history and coverage, initial
interner validity, successful original construction, edge residency, ready
inherited storage, actual live prefix receipt, reached machine-word ranges,
and initial fourth-memo Correct. Empty fourth-memo correctness can be
instantiated with the existing empty_correct theorem.

There is no supplied future Scan, caller completion callback, final Good,
future field load, desired class law, or whole-forest closure premise.
The live prefix condition preserves the source empty and contradiction
branches as separate cases. This endpoint does not assert that every
precheck returns live classes.

Exact original-witness inclusion in the seeded query still requires semantic
admission for generated operands and warm-cache law transport. Source lazy
execution, pending publication, actual identity correspondence, and external
solver behavior remain adapters. No Haskell or runtime claim was added.
