# Full empty-own local range validation

Validated at 2026-10-16 15:21 CEST with pinned Lean `leanprover/lean4:v4.34.1`.

Source: `lean/MicroCFTA/SourceCurrentAllocatedLocalPlainRanges.lean`, 79 lines.

SHA256: `f0d2c5717ae7e7f67b77956e3fc1cec7de2517f8fdda3d75091a44bb42976c08`.

## Derived range plan

`nil_ranges` constructs both fields of `SourceCurrentConjunctionScanClassPass.Ranges`. The empty Scan range is `True`. In its continuation field, the actual nil Scan and its exact positional `Retained` receipt force the kept records to be empty. The class-pass range is then `ClassPass.Ranges.nil`. The proof does not use the supplied required-worker completion equation or its returned forest and heap to establish a result law.

`ranges` uses the actual accessor/precheck `prefix_cases` to exclude every reached nonempty record list. Unchanged and empty-child branches contradict the reached class equation. The remaining reached list is exactly empty. Thus the theorem derives the full finite `LocalReduction.Ranges`, including class continuation ranges. It does not merely derive the smaller `LocalReductionActual.Ranges`.

Its inputs are current operation validity, stored and inherited equality readiness, and effective `OwnEmpty`. The inherited payload is arbitrary. No positive bound, forest availability, forest closedness, native range plan, successful local execution, final invariant, or future semantic callback is supplied.

`loaded_ranges` derives stored readiness and effective own emptiness from the actual same-cache field load and the original effective equality test. `resident_ranges` derives the parent range plan from the current physical edge annotation. Its effective equality test is conditional on the actual live raw branch. The raw rejected branch demands no field load or own-empty test in this range plan.

## Checks

- `localplain-ranges-direct-1.log`: exit 0, no warnings or errors.
- `localplain-ranges-build-1.log`: root-managed canonical build, success, 1489 jobs. Only the historical dependency warning remains.
- `localplain-ranges-probes-1.log`: imported-module external check, exit 0, no warnings or errors.
- Four public theorem axiom reports and full signatures pass.
- Four integration kernel axiom reports and full signatures pass.
- All eight final reports contain no `sorryAx`. Their axiom union is the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Integration kernels

1. Derived full local ranges feed `LocalWorkerActual.finite`. Initial caller context, actual same-cache load, inherited readiness, available input forest, and effective own emptiness derive stable literal execution, full caller `Post`, and original-or-erased shape. No range plan is an input.
2. Derived resident ranges feed `ParentWorkerActual.resident_finite`. Initial context, inherited readiness, edge residency, and live effective own emptiness derive the actual same parent body, strict source reads, full caller `Post`, result residency, and its independent inherited edge law. No completed parent body or range plan is supplied.
3. The full nil continuation range applies to the exact actual Scan, positional retained records, and required-worker prefix. This checks the class-pass component that the smaller actual range type omits.
4. A contradictory inherited payload still derives the full finite local range plan. The theorem does not silently require empty inherited equalities.

## Scope

Effective own emptiness includes positive guard equality extraction. Stored raw empty equality fields alone do not establish it. Residual guards, actual prefix allocations, current native tables, and warm memos retain their existing definitions.

This is a local finite-plan theorem and an adapter to existing current parent completion. General recursive caller progress and concrete host forcing/publication correspondence remain separate. No older proof, Haskell source, Audit, restart authority, or Git state was edited. No Haskell run or network request occurred. Root owns canonical builds and publication.
