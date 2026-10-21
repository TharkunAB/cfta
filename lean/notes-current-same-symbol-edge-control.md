# Same-symbol comparison control

## Same-symbol comparison control

Updated: 2026-10-22 00:21 CEST. Proof checkpoint: `a1bc2fada4`.
Start: `e03b78047a`. Imported main remains `794903b3f`.
Read `lean/notes-current-same-symbol-edge-control.md`.

SourceCurrentSameSymbolEdgeControl.miss_readback proves the provenance of
an observed successful comparison when BOTH ordered pair keys were absent.
Its state retains the complete checked native state and a separate typed
pair memo. It publishes the original pair before demand and operand order.
A reversed call publishes a second pair and retains the original handle.
Explicit return steps finish the inner cell and then the original cell.

The theorem returns an actual direct native edgeBody trace at emptyDomain
from the SAME before.checked to after.checked. The original captured cell
contains the result. A strict reversal also has a distinct reversed cell
with that same result. All earlier returned cells remain. Unrelated memo
entries and the native tables may already be populated.
Premises are structural memo validity, both missing keys and observed
completion. No semantic meet, Room or future-success premise is added.
This theorem does not produce completion or a warm-hit historical law.

The module has 334 lines and one public theorem. Strict3 passes at default
declaration limits with linter.all and a literal empty log. Sole FULL1 has
449 logical TYPE lines, 448 LF characters and no final LF. Its checked and
printed TYPE bytes match: 34826 bytes and 34814 Unicode characters.
All eight private helpers and four private markers are absent from TYPE.
Actual axioms are the standard three. FULL1 retains 6247397 raw bytes.
Root and independent review covered the complete TYPE. The 6177481-byte
body is retained and checked programmatically; no whole manual read is claimed.
Audit passes: 3624 jobs /75337 theorem dependencies.

Five actual Lean/Lake commands remain: strict1 failed with six errors and
two warnings; strict2 exited zero with one deprecation warning; strict3
is clean; FULL1 and Audit1 pass. Audit only repeats the old inputs warning.
The six proof repairs and one deprecated-lemma replacement remain as exact
deltas. Earlier drafts, the inequality correction and added documentation
remain. The stopped first FULL materializer is metadata, not a FULL run.
Root corrected its premature empty-log commentary about strict2.

The strongest combined semantic theorem remains constructed_node_calls:
any chosen finite number of actual modeled partial reductions from a
constructed covered input, with successful continuous state and exact
finite-term language under the formalized guard semantics.
The complete withoutRedundantEdges pass is not included.

The next direct-edge semantic inventory and its independent audit are
source-only. Existing receipts retain the result and complete checked
after-state. Resident-edge growth and empty_domain derive readiness for
the next original cluster pair. Current admission, completion certificates,
sequence fuel/width/WordRanges and separate pair-memo hit history remain.
The actual ruleOut scan, cluster reconstruction, recursive Mu mapping,
whole public pass, convergence, practical fixed width, external solver
composition and Haskell refinement remain open.

All old proofs, counterexamples, marked drafts and optimized code remain.
The only old Lean edit is one Audit import. All 268 Haskell files and 207
active package files remain unchanged. No Haskell repair or runtime change
is claimed. FINDINGS retains the external Haskell repair index FIRST.
Work continues.
