# Original-budget native admission

Status: READ-ONLY audit. The proposed header is UNPROVED. No Lean file was compiled or changed.

The exact engine inputs are `SourceCurrentAllocatedNativePhysicalExecution.InputsThrough` and `SourceEqualityNativeDemandOperations.FieldsThrough`. They are different predicates. This packet does not call either predicate `OriginalInputsThrough` or assign it a semantic Profile meaning.

## What already has a source producer

`SourcePruningEnumerationNativeRequestInputs.inputs_of_resources` (line 50) already derives the physical `InputsThrough nativeFuel` plan for the literal empty-domain request. Its inputs are the current `Context`, `Fits`, old numeric `Room`, and closed Available operands. It retains the full current native tables. It does not take a future trace, result law, or a new budget.

The proof calls `SourceCurrentAllocatedTargetQuery.finite_caller_resources` (line 29), then extracts `receipt.actual`. Its private `trace_inputs` (line 28) proves the plan for EVERY supplied `nativeFuel` from that internally constructed physical trace to pure. At pure, no later input obligation is required. This argument retains small and zero budgets. It does not run the algorithm at a larger budget in the claimed conclusion.

The source call sites are real. `DispatchGuardHeap` (line 88) and `IncomingGuardHeap` (line 70) already use this producer. Shared dispatch runs the literal empty-domain request on the two decoded pending operands. Shared incoming runs it on `incoming` and the decoded stored operand. `PendingRealized` supplies the stored value's availability and closedness. Source preparation supplies the incoming value's availability and closedness.

## Smallest missing field-plan producer

The proposed `fields_of_resources` header retains EVERY explicit input of `inputs_of_resources`. It changes only the output to the exact `FieldsThrough nativeFuel` predicate consumed by `GeneralCMHistory` and `SourceQueryInduction`. No proof is included.

Its concrete derivation needs one weak physical induction, not another observer:

1. Obtain the exact physical plan from `inputs_of_resources`.
2. Take `initial.ready.good`. The literal request's initial allocated-field predicate is already proved by `NativeRequestGuardHeap.request_allocated` (line 29).
3. At each actual control, `NativeFieldClosure.operation_fields` (line 40) derives the normalized field check from current `Good.fields` and current allocated control fields.
4. `NativePhysicalCompletion.step_invariants` (line 129) retains `Good` and the actual yielded continuation's allocated fields. Recur on the remaining ORIGINAL plan and budget. A terminal, error, or blocked result requires no later field premise.

The first concrete control where this matters is `.edgeBody request next`, reached by a genuine evaluating edge request. Its required field predicate is cached normalization of BOTH original guard equalities. It is not availability of a future combined guard. Current resident original rows plus the current allocated field heap derive it.

`NativeFieldExecution.execute_invariants` (line 51) already returns a field plan, but it requires semantic `StateValid` and `SourceEqualityNativeDemandFieldExecution.InputsThrough`. Those inputs include produced-result finish receipts. They are NOT the weak physical plan above. Using them as a shortcut would add a different semantic obligation. The proposed weak induction avoids that substitution.

## Current numeric admission is broader

The old physical plan API takes `Room`. Actual shared dispatch/incoming resource APIs now take `Admits = Room ∨ Entry` (`NativeCreditProfile`, line 25). `Entry` must not be silently treated as `Room`.

There is a concrete source route for BOTH alternatives. `SourceCurrentAllocatedTargetQuery.ready_admitted_ranges` (line 29 of `TargetCallerCreditResources`) derives actual `WordRanges` from current `Ready`, `Fits`, `Admits`, and closed Available operands. `NativePhysicalTraceCompletion.initial_complete` (line 535) then constructs its own physical trace from current Good, idle, closed original operands, and these derived ranges. `closed_original` derives Original from current coherence/availability/closedness. A small trace-to-plan induction yields any ORIGINAL nativeFuel, exactly as the existing private `trace_inputs` does. The same weak field induction supplies `FieldsThrough`.

Thus the final Admits version can have only current Ready/Fits/Admits/closed Available operands as inputs; it need not require inventory, a future trace, or a Returned law. This is an API derivation still to implement. `WordRanges` alone is not the physical plan.

## What remains a separate semantic task

Both original-budget plans are operational admission. They do not prove either inherited `Returned NodeResult` or `Returned EdgeResult`. Retained/local producer provenance also does not prove those laws. The chronological induction must derive the old priors from real earlier calls and qualify each new producer against the fixed whole history, including entries later than cell birth.

Current `Context`, `Ready`, resource bounds, and operand witnesses must come from the actual source caller/worker producers at the exact native call. Their existence must not be inserted as a new arbitrary warm-state assumption in the final end-to-end theorem. Available API inputs do not establish all arbitrary warm states. Nested enabled checks and target forcing remain real chronological calls; they cannot be skipped in an induction over source operations.

The original one-assignment, one-finite-accepted-completion theorem for the same emitted root and ALL retained/historical obligations remains open. No Haskell change or bug is claimed.
