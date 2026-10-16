# Independent review: local worker stable completion

Reviewed source: `SourceCurrentAllocatedLocalWorkerCompletion.lean`, SHA256
`fd777126b4cd015a046469ec2192d0e6c3329fdee89cc7a6720fe6885b785134`.
No material defect was found. No proof source changed during this review.

## Same execution and record occurrences

`classes_complete` consumes the supplied current Reduction. The completed
branch uses that exact Scan, its exact positional Retained receipt, the
literal required-worker return, and the supplied class Pass. RecordScan's
completion executes those retained Record occurrences. The proof never
recovers records by set filtering or equal-path choice. `retained.fields.2`
only reads back the selected paths of these same records.

The required worker starts at the Scan-return heap on the original values.
The Pass starts at the literal `advanceHeap` of the required return, on the
required values and warm merge memo. ClassWorker's Pass executes the right
fold and final empty propagation. Its return is the exact Checked and merge
memo in the local graph. The fourth memo comes from the same Scan.

The stopped branch uses that same Scan and returns erased original slots.
Its structural required, edit, merge, and comparison bounds are zero. It
supplies no completed required or class callback. The unchanged and
contradictory prechecks also use zero continuation bounds.

## Bound composition

The nine bounds are g/s/r/e/p/h/m/c/n. In the live completed branch, p is the
maximum of the Scan and class projection bounds. h is the maximum of Scan,
required read, and class read bounds. n is the maximum of Scan and class
native bounds. The structural required and class edit bounds stay separate.
Merge and comparison bounds come only from the reached class Pass. The
conjunction budget is a fixed parameter throughout. The proof applies each
stable component at the same final maxima and at its exact prefix state.

`required_complete` reconstructs the actual Required graph from the supplied
literal success, then uses graph completion. It needs no physical or closed
input. `reduce_complete` retains the actual precheck operations through
`Precheck.state`. It neither resets the native machine nor chooses a new
precheck result.

## Current source and scope

The branches match `Equality/Operations.hs:207-226`: empty constraints,
contradiction, refused-class early stop, then requireAll on origNs and the
class right fold with final propagation. The seeded ordering matches the
source helper at lines228-230. The completed serial graph is the input of
this theorem. This module does not by itself construct that graph from
initial physical facts, prove failed-outcome monotonicity, or establish GHC
demand/heap scheduling. Global read receipts are composed by the separate
Actual layer, not executed by this worker.

## Independent checks

The final external pinned Lean probe returned exit0 with no warnings,
errors, or sorryAx. It checks all three public theorem axioms/signatures and
five kernel integrations: stopped execution at zero continuation bounds,
exact positional records through Required and Pass, actual nine-bound
literal execution, unchanged precheck, and contradictory precheck. Only
standard Lean foundations occur in the axiom reports. No Lake process ran
for this review.
