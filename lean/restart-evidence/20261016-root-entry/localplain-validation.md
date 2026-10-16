# Empty-own local worker validation

Validated at 2026-10-16 15:09 CEST with pinned Lean `leanprover/lean4:v4.34.1`.

Owned source: `lean/MicroCFTA/SourceCurrentAllocatedLocalPlain.lean`, 129 lines.

SHA256: `32a24685f740cd20b80eed3af2684251baa0859ed399f0fc3ad77a214e3c4ba3`.

## Result

`OwnEmpty loaded` tests the complete source accessor, including positive equality extraction from `loaded.guard`. It does not merely test the stored equality payload. Exact original readback and successful same-cache field loading transfer the original effective equality test through `of_readback` and `of_load`.

`prefix_cases` derives actual accessor and allocated precheck completion from valid current operations and ready stored and inherited values. Its only possible branches are unchanged, erased children, and the empty own class list. The arbitrary inherited value need not be empty.

`empty_stages` proves the current literal empty Scan, required-path worker, and class pass. Required structural work is the identity. The final class pass executes empty propagation. These stages retain the entire checked state and both warm memos.

`complete` constructs literal local worker success at every nine-bound tuple, including all zeros. It retains the exact actual prefix operation state, the full native state, fourth memo, and merge memo. The returned forest is the input forest or its erasure. It takes no forest availability, closedness, reached range, completed callback, successful execution, or output-shape premise.

`done_shape` identifies every supplied literal success with this constructed result. It derives the full checked-state equality, fourth and merge equality, and the same original-or-erased shape.

Only the pure `precheck_cases` and `propagate_shape` facts are reused from `SourceEqualityPartialInheritedPlainPass`. No historical source execution, native worker, or graph equivalence is transferred.

## Checks

- `localplain-direct-2.log`: exit 0, no warnings.
- `localplain-build-1.log`: root-managed canonical success, 1416 jobs. Only the older dependency warning remains.
- `localplain-probes-1.log`: external imported-olean check, exit 0, no errors or warnings.
- Six public theorem axiom reports and full signatures pass.
- The public `OwnEmpty` definition signature passes.
- Six integration kernel axiom reports and full signatures pass.
- All twelve reports contain no `sorryAx`. Their axiom union is `propext`, `Classical.choice`, and `Quot.sound`.

The first direct log records a path-list simplification error and two argument-count errors. These were corrected before the source freeze. That failed log remains available.

## Integration kernels

1. A resident physical edge and initial checked readiness derive its current field load and zero-bound local completion. No child-domain or range premise is supplied.
2. Supplied local success retains the full native state and returns the exact actual accessor/precheck operation state. Both warm memos stay equal.
3. The derived child-list shape discharges `PartialActiveOrder.original_or_erased_bound`. This is the returned-edge structural hook; it is not a general caller progress theorem.
4. Under the same initial equality facts, no literal failed observation is possible at any bounds.
5. A forest containing an arbitrary reference still completes at zero bounds. The local worker does not demand that reference in this domain.
6. The literal empty Scan, required, and class-pass stages complete at zero bounds with the source's final propagation result.

## Scope

The theorem keeps residual guards and actual prefix allocations. It does not replace the current equality interner or operation tables. A stored empty equality payload alone does not satisfy the effective own-empty premise when guard extraction adds equalities.

This closes this local completion and shape case. General recursive caller progress, publication, concrete source memo/CAF transfer, and GHC demand order remain separate. No Haskell change, network request, Git mutation, older proof edit, Audit edit, or Haskell run occurred in this task.
