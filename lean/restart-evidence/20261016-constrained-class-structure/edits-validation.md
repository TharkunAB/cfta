# Current edit structural validation

Validated on 2026-10-16 in the pinned Lean 4.34.1 environment.

`SourceCurrentAllocatedFiniteOrdinaryReceiptStructure.lean` has 134 lines.
Its SHA256 is `847083165bf6074c526a9e7e64167c485ed565b1004d80753130f3c2b8cf1464`.
`SourceCurrentAllocatedFiniteOrdinaryEdits.lean` has 294 lines.
Its SHA256 is `e993be13afde0b8bcd68d649c1804a8ce8277ed881d67898eaac97bd14e395ad`.
Both sources are frozen.

The receipt helper derives structural facts from actual target reads and force/leaf receipts.
The current initial capture base is independent of a nested receipt's historical base.
The helper uses the actual reached physical query trace.
Its leaf bound refers to the second native operand, which is the current edit input.
No uniform range plan is an input to these supplied-receipt endpoints.

The edit proof uses the actual mutual node, child, and row read receipts.
It derives current inventories from the existing physical effects at each prefix.
Raw row reconstruction retains full guards and ordered children.
Raw node reconstruction uses the actual resident rebuilt rows.
The finite ordinary domain excludes recursive head cases.
The conclusion retains native, merge, and target-slot structural certificates at the same returned state.
Its positional `All₂` relation bounds each output by its own original input height.

Direct source checks:

- `edits-receipts-direct-2.log`: exit 0, no warnings.
- `edits-direct-3.log`: exit 0, no warnings.
- Earlier direct logs retain corrected namespace and definitional-reduction errors.

Root ran the canonical focused builds and observed terminal exit 0:

- `receipts-build-1.log`: 1300 jobs, process 89785.
- `edits-build-1.log`: 1306 jobs, process 84483.

The canonical logs contain only the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`.
No new module warning occurs.

Imported public checks in `edits-public-1.log` pass with exit 0.
They contain 8 public axiom checks and 8 full signature checks.
The only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` occurs.

`edits-kernels-3.log` passes with exit 0 and no warnings.
It contains 8 named integration proofs, 8 axiom checks, and 8 signature checks.
The proofs check the current-input leaf bound, independent historical receipt bases,
ordered forest domain/arity/height, two serial actual list traversals,
ignored root callbacks, actual ordinary reconstruction, unrestricted row guards,
and a slot read at the exact returned state.
Earlier kernel logs retain corrected implicit graph indices and a well-founded `Populated` reduction.

These are structural verification endpoints for supplied actual reads.
The existing class finite endpoint constructs those reads from initial facts and reached checks.
This module does not assert outer recursive termination or a GHC allocation schedule.
No older proof source, Haskell source, Audit, documentation authority, or Git state was changed by this task.
