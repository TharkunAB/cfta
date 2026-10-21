## Current outer prefixes preserve closed inputs and node results

Updated: 2026-10-21 13:44 CEST. Proof checkpoint: `7bbc88f746`.
Start: `671fd6df46`. Imported main remains `794903b3f`.
Read `lean/notes-current-outer-closed-inputs.md`.

OuterClosedInputs.reached now preserves BOTH conditional node-result
closure and closure of the literal inputs at every actual outer prefix.
The exact public API contains NodeStored, InputsClosed, initial and reached.
Closed means Value.free=[]. Bound references inside an opaque Mu remain
permitted. Availability alone does not imply closure. The initial theorem
supplies NodeStored from the actual empty outer node table.

The theorem keeps the genuine initial Context, Frame, Fits, carrier,
ready inputs, scheduled Room, native/Merge laws and resource writer Origins.
It adds initial NodeStored and InputsClosed. It needs no initial node-idle
premise. Unused open cells remain permitted. A returned node cell requires
closed captured input to imply a closed result. This conditional store law
is preserved by actual lookup, demand and finish operations.

The same coherent current heap identifies the complete captured value
with the candidate at ready and evaluate observations. A cache hit uses
its actual stored conditional result law. Evaluation derives closure of
the same captured input before entering its body. The actual closed body
result supplies the finish law at the literal handle. Parent children use
the same historical Written witness and the checked ParentClosed theorem.
No new edge-cache ledger or desired returned-closure callback is supplied.

One local completed-call induction covers all six concrete phases. The
same initial packet stays in scope. Existing resource and Origins producers
are applied to each SAME global Reached cut. Earlier completed siblings
supply their actual done equations. Real returned availability supports
physical node and edge reconstruction. Existing Mu cleanup preserves free
references. The final eight-case prefix induction uses those actual
completed-call facts. No future enclosing return is assumed.

The next failure consumer must extract the actual reference-body or absent
node-demand cut from a literal failed run. These inverse cuts are still
unproved. At the reference cut, reached closure would contradict the
singleton free-reference list. At the absent cut, existing reached table
validity suffices: a hit has a cell and a miss publishes a suspended cell.
One combined public consumer and one local joint inverse are reviewed.
Its source plan requires an official compiled closure dependency, separate
activation, and a stop at 250 total lines before ANY compiler or further
implementation. Whole source review precedes a separate check activation.
The frozen plan retains its historical pending-dependency statement.

Every-active-node busy exclusion remains checked under initial idleness.
The largest completion gap remains a first sufficient outer fuel jointly
with a noncircular INITIAL capacity envelope. Chosen-fuel scheduling and
stability of an existing success do not construct one. Finite renewals,
final retention, completion, convergence, broader initial resources and
Haskell refinement remain open. Whole-library termination is not proved.
The broadest semantic claim remains exact finite-term language preservation
for a supported SUCCESSFUL traversal with empty inherited constraints.
General inherited constraints give narrowing, with exactness under
inherited satisfaction.

Selected strict6 and root strict have empty logs. Complete FULL, independent
review and Audit pass: 3612 jobs /75069 dependencies. Nine actual Lean/Lake
commands retain five failed author strict checks. Strict1 alone has two
warning diagnostics. Every raw input, log and exact repair remains. The
selected source has 420 lines; all four public shapes remain unchanged.
Original 231/386/417-line prelaunch sources and zero-job patches remain.
Whole public type identities and all eight printer settings pass. Actual
axioms are propext for NodeStored and initial, none for InputsClosed, and
the standard three for reached. No canonical, infrastructure, constructed,
runtime or reviewer proof job ran. Only the old Audit warning remains.
Counts are not completion. Four frozen proof/review/next-plan components
have portable and mandatory live verification. All older evidence remains.

Haskell, packages, imported main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its external repair index
FIRST. Work continues as requested.
