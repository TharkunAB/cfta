# Checked demand node-counter growth

Updated: {now}. Proof checkpoint: `{proof}`.
Start: `86b6dd30387c62a1f8f46e1914824695c4a0e908`.

The theorem step_mono compares the initial physical constructor node counter
with the counter in the actual checked-demand step outcome.
The theorem execute_mono gives the same bound for every finite fuel.
The theorem resume_mono compares the state of a supplied outcome with the state
of its actual resumed outcome. All five checked-demand outcome tags are included.
These tags are yielded, done, failed, constraintError and blocked.

The statements permit arbitrary controls, output types, states, widths and finite fuel.
They require the existing equality instances for Symbol and EdgeKey.
They require no validity, readiness, success, callback-bound or desired-counter premise.
The code branch uses H35 native step_mono on the actual native state.
A private helper proves that lifting each native outcome retains its complete state.
The direct edge branch uses the checked-demand heap observation.
The edge-body branch uses its exact native-state observation.
The fuel induction uses the actual yielded control and full state at predecessor fuel.
No definition, predicate or global instance is added.

The single 80-line variant passed its first strict check under default limits.
All linters were enabled. The strict log is empty.
The sole FULL check retained all 696507 bytes of actual output.
Root and an independent reviewer read the complete checked TYPEs.
All 12 TYPE, printed TYPE, BODY and axiom slices reconstruct the raw log.
BODY retention was checked programmatically. No whole printed BODY read is claimed.
All TYPE pairs have actual raw byte identity and four-ASCII-whitespace lexical identity.
Both raw hashes are retained. All three actual axiom reports contain only
Classical.choice, Quot.sound and propext.
Audit passed with 3655 build jobs and 75560 theorem dependency checks.
One older unused-variable warning was replayed. The new source has no warning.
The complete ledger has three jobs, two source jobs and one Audit job.
It has no failed job, warned source job or rejected public TYPE.

This result gives a node-counter lower bound. It gives no allocation upper bound.
Pair/Scan/H23 lifting, fixed-source initial counter order and global domain-history
transport remain separate. Room, WordRanges, complete resources, generated
execution, Mu/full pass, practical width, Haskell and solver correspondence,
and convergence remain open.
H6 constructed_node_calls remains strongest combined.
The goal is ACTIVE and incomplete.
No Haskell repair is required by this checkpoint.
FINDINGS retains both imported repairs and all earlier evidence.
The baseline contains 120276 files/modes, 3653 older Lean sources,
298 Haskell files and 207 package files.
This note precedes the final seal and push. It claims neither result.
