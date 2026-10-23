# Row cluster scan node-counter growth

Updated: 2026-10-23 19:12 CEST. Proof checkpoint: `27cebaf220e74265207cef19212d40fb08ece98f`.
Start: `527a5cd981b6b406cf7078ac2fe96c288379afb7`.

The public outcomeState returns the complete existing Pair.State from every Scan outcome.
It needs no equality instance and has no axioms. The step_mono and execute_mono
heads carry only the existing DecidableEq Symbol and DecidableEq EdgeKey instances.
Their inputs allow arbitrary width, control, full state and finite fuel.
The conclusion compares nodes.next in the input checked native heap with that
counter in the SAME actual Scan result. It includes yielded, done, failed,
constraintError and blocked results. It requires no validity, readiness, success,
callback bound, final-counter certificate or replacement state.

The four cluster/scan list cases keep the input state. The comparison case uses
H37 step_mono at the same Pair.step inner control and state. Every Pair outcome
passes its actual after state into the Scan outcome. Pair.done becomes Scan.yielded
with conditional control. Reading the state does not need an identity test split.
The fuel IH generalizes the complete control and state. Its only call is
`ih next after` at predecessor fuel in the actual yielded branch.
The result is a non-strict lower bound. It does not assert equality of other state fields.

The unchanged 80-line source passed its first strict check with an empty log.
The sole FULL job passed and retained 656026 raw bytes.
Root and an independent reviewer read the complete checked TYPEs: 2, 35 and 35 lines.
All twelve retained slices reconstruct the entire raw output.
BODY retention was checked programmatically. No whole manual BODY read is claimed.
Raw TYPE byte identity is false for outcomeState, true for step_mono and false for execute_mono.
Four-ASCII-whitespace lexical identity holds for all three. Both raw TYPE hashes remain retained.
The accessor axiom set is empty. Both theorem sets contain Classical.choice, Quot.sound and propext.
Audit passed with 3657 build jobs and 75584 dependency checks.
It replayed the known older unused-input warning. The new source has no warning.

The actual history cut has three successful proof jobs: strict, FULL and Audit.
It contains one unchanged mathematical variant, zero patches and zero rejected public TYPEs.
The collector retains 924 artifacts and 21 Root metadata attempts, including one failed reader
attempt and its successful retry. The metadata failure is separate from Lean proof jobs.
The collector receipt and later closing receipts remain outside that historical cut.
The one-time final support collection retains those later records.
No Haskell repair is required. Earlier implementation, proof bodies and counterexamples are unchanged.
The Audit file adds the one selected module import.

A reviewed source-only route identifies a consumer of the SAME H23 finite Scan chain
and literal checked work2 rebuild. It adds no checked consumer at this checkpoint.
The new H23 counter join, fixed-source initial counter order and new global-domain-history
composition remain separate. The earlier H23 conditional completion, domain-Trace
and language-preservation results remain proved under their stated premises.
Complete upper resource bounds and full-pipeline Room/WordRanges, generated execution,
Mu/full pass, practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
This note precedes the H38 seal and push. It claims neither result.

## Selected sources and complete public types

lean/MicroCFTA/SourceCurrentOriginalRowClusterScanNodeCounterGrowth.lean: 80 lines, SHA 7db9cd645899e31a3f04149e0ea8bd27f8e5c55c336aab872f8c286c04822cb7.

MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.outcomeState: 2 TYPE lines, 141 bytes, SHA 07bda9847d6e6ae0e9f75d916aed0fea6213d546fce6b175b29138c6220ed05e.
Printed TYPE SHA 61f6f2dc08c95fef087bd421fd3c3035e355253d4daf167fed07e524736dac65. Raw byte identity: False. Lexical identity: True.
Actual axioms: none.
MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.step_mono: 35 TYPE lines, 2535 bytes, SHA 69ac91638b3215e8fdad0d04b0cafc6f135436d1284005c6f0da074e9e6c940d.
Printed TYPE SHA 69ac91638b3215e8fdad0d04b0cafc6f135436d1284005c6f0da074e9e6c940d. Raw byte identity: True. Lexical identity: True.
Actual axioms: Classical.choice, Quot.sound, propext.
MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.execute_mono: 35 TYPE lines, 2556 bytes, SHA ec95ff3c3e060b0cf359123b7e08804b015764efe445a3dba5e0fe5616c5e750.
Printed TYPE SHA c256a98bcf6dbbb48d0b129af79aee10f50f6144e6bbbdc7837b8b88c493e6b2. Raw byte identity: False. Lexical identity: True.
Actual axioms: Classical.choice, Quot.sound, propext.
