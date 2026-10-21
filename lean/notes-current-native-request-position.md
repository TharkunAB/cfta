# Actual native requests and positive child paths

The top-level goal remains a proof that the optimized interned CFTA operations
implement the intended language semantics, maintain their invariants, and
complete under the intended finite conditions. The Haskell implementation
still needs an explicit correspondence proof. This checkpoint proves one
conditional native-execution property needed by the outer equality proof.

## Current statement

Module: `SourceCurrentNativeRequestPositivePositions`.

`Support source native` states two valid memo-table invariants.
For a returned node cell, legitimate original bindings and source inputs
with finite Plain caps imply this law: each positive result occurrence at a
natural child path comes from one captured input at that same path.
For a returned edge cell, the root guard and ordered child occurrences obey
the corresponding two-input law. The definition retains bounded and linked
table facts. It uses the full captured requests.

`call` consumes an actual completed empty-domain native request trace.
It derives Support for the final tables, the same-path result law, the old
physical and finite-cap Return, and actual causal Mu history for the final heap.
The entry tables must satisfy the old store law and Support. These are laws
for past returned cells. The theorem does not assume the desired future result.

`request` starts with empty native tables.
It derives both entry cache laws and applies call to the actual trace.
Its input operands are source-resident, closed, and bounded by a finite cap
whose Mu guards are Plain. Entry Good, SemanticReady, GuardHeap Plain and
actual causal Mu history remain premises. The theorem does not manufacture
a successful trace or assert termination.

PositiveAt observes an ordinary row with a nonplain full guard.
It follows natural child indices and descends through unions at zero path
cost. It treats Mu and references as opaque. Different result occurrences
can select different input sides.

## Actual execution facts

The private induction follows the supplied physical Trace.
Each smaller body uses the SAME existing cap certificate and the new position
certificate. Each node or edge finish installs both laws for the SAME owner,
captured request, body and result. Ready hits recover full request equality
from PhysicalCache.Valid and KeySafe. Key equality alone is not sufficient.

The proof carries actual causal history at intermediate cuts.
It uses actual guard loads and conjoin allocation, exact ordered child
correspondence, and the existing maybeMu and substitution position theorems.
It covers ordinary, nullary, union, Mu, reference, self, swap, repeated,
decision-reset and returned-cell branches. The optional-binder cases use
actual publication history. They do not equate an old winning memo body with
the current callback body.

## Validation and preservation

The source has 1,193 lines and SHA-256
`e62eed872e07c2457a0ae577e7e35281b48fe4d5ebc6b90bbb403a62e01c5727`.
Root strict checking has an empty log.
Complete printing of Support, call and request has no omitted body or type.
All three heads report only propext, Classical.choice and Quot.sound.
Independent review read the full source and the final changes.

The main package has five actual Lean jobs and three failed attempts.
The separate edge helper has four jobs: two failures, one warning-bearing
unselected success, and one clean selected success. Root strict and the
default Audit add two jobs. Copies and zero-job reviews add no jobs.
The total is eleven actual Lean/Lake jobs with five nonzero exits.

The checkpoint retains every older proof and evidence file.
It preserves Haskell and package files, older frozen registries, stashes,
other worktrees and main. FINDINGS retains its external Haskell repair
registry first. There is no new Haskell defect or repair.

## Remaining work

A small next theorem must rebase Support to a later source using actual
origins for the SAME captured node and edge cells. It cannot infer origins
from Support or Grows alone. That theorem is separate from this checkpoint.

The larger gap is selected-observation transport through one complete class.
The current native law tracks visible positive occurrences. It does not by
itself recover observations hidden by opaque Mu or identify a changed
phaseValues forest with the original prepared forest. The proof must retain
the selected observation through actual Head and native continuations.
Original false class gates remain gates on their original values.

After that, the proof must compose chronological class edits, establish the
retained conflicting pair or exclude the owner, and prove general renewal,
final retention, outer completion and convergence. Haskell correspondence
also remains open. The unrestricted opaque-Mu counterexample remains valid;
the finite-cap premises are essential to the current theorem.


Selected proof: `c5055d40de6caf6e3cd2c71062ef3905c81b16ea`. Updated: 2026-10-21 03:55 CEST.
Default Audit: 3565 jobs and 74712 theorem dependencies.
Actual Lean/Lake jobs: 11. Nonzero jobs: 5.
