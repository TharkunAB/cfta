# Native node-counter growth

Updated: 2026-10-23 15:29 CEST. Proof checkpoint: `a0a671b5c3cfd7a000a5298f74603c05a48f1702`.
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

## Selected sources and complete public types

lean/MicroCFTA/SourceRecursiveIntersectionNativeNodeCounterGrowth.lean: 79 lines, SHA b43e0c75517bb57db8a062d45c2282c9117ce3944d5086d323318790a8fb9bec.

MicroCFTA.SourceRecursiveIntersectionNativeNodeCounterGrowth.step_mono: 17 TYPE lines, 1291 bytes, SHA 9acac99616c09dee7d4d881c14d2973ea0c9fe14225279421402147794138e0c.
Printed TYPE SHA 9acac99616c09dee7d4d881c14d2973ea0c9fe14225279421402147794138e0c. Raw byte identity: True. Lexical identity: True.
Actual axioms: Classical.choice, Quot.sound, propext.
MicroCFTA.SourceRecursiveIntersectionNativeNodeCounterGrowth.execute_mono: 17 TYPE lines, 1312 bytes, SHA b4da01426ccf580e128dfacd86e0c946722ee78f2ce8afcdc200661858983ee0.
Printed TYPE SHA 9d099af66e5fdf0c209f306b00075eb15d074e3f0b85efd3f342bc923e586571. Raw byte identity: False. Lexical identity: True.
Actual axioms: Classical.choice, Quot.sound, propext.
MicroCFTA.SourceRecursiveIntersectionNativeNodeCounterGrowth.resume_mono: 18 TYPE lines, 1339 bytes, SHA 8189d8f7e689baf3fe36b972cb94f97c83d988da9750130d60b19cb15d16542a.
Printed TYPE SHA b46e875af607ef6c62b49b9d9e0ea62a90fb236416c20949392b23adc4d58db6. Raw byte identity: False. Lexical identity: True.
Actual axioms: Classical.choice, Quot.sound, propext.
