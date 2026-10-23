# Native node-counter growth

Updated: {now}. Proof checkpoint: `{proof}`.
Start: `a295f1f72153365c886484cbeea933809acbc3f7`.

The theorem step_mono compares the initial physical constructor node counter
with the counter in the actual native step outcome.
The theorem execute_mono gives the same bound for every finite fuel.
The theorem resume_mono compares the state of a supplied outcome with the state
of its actual resumed outcome. All four native outcome tags are included.

The statements permit arbitrary code, states, widths and finite fuel.
They require the existing equality instances for Symbol and EdgeKey.
They require no validity, readiness, success, callback-bound or desired-counter premise.
The proof uses actual Work reservations and the H34 optional-binder bound.
Pending constructor work uses its actual returned heap.
The fuel induction uses the actual yielded code and state at predecessor fuel.
No private helper, definition or predicate is added.

The single 79-line variant passed its first strict check under default limits.
All linters were enabled. The strict log is empty.
The sole FULL check retained all 214732 bytes of actual output.
Root and an independent reviewer read the complete checked TYPEs.
All 12 TYPE, printed TYPE, BODY and axiom slices reconstruct the raw log.
BODY retention was checked programmatically. No whole printed BODY read is claimed.
All TYPE pairs are equal after four-ASCII-whitespace normalization.
Their actual raw byte identity flags are true, false and false, in public order.
Both raw hashes are retained. All three actual axiom reports contain only
Classical.choice, Quot.sound and propext.
Audit passed with 3654 build jobs and 75556 theorem dependency checks.
One older unused-variable warning was replayed. The new source has no warning.
The complete ledger has three jobs, two source jobs and one Audit job.
It has no failed job, warned source job or rejected public TYPE.

This result gives a node-counter lower bound. It gives no allocation upper bound.
Scan/H23 lifting, fixed-source initial counter order and global domain-history
transport remain separate. Room, WordRanges, complete resources, generated
execution, Mu/full pass, practical width, Haskell and solver correspondence,
and convergence remain open.
H6 constructed_node_calls remains strongest combined.
The goal is ACTIVE and incomplete.
No Haskell repair is required by this checkpoint.
FINDINGS retains both imported repairs and all earlier evidence.
The baseline contains 118574 files/modes, 3652 older Lean sources,
298 Haskell files and 207 package files.
This note precedes the final seal and push. It claims neither result.
