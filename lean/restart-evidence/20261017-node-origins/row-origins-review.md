# Required structural row origins

The final source is `SourceCurrentRequiredRowOrigins.lean`, SHA256
`b06879776627e2fcabc360252ed872be7537db32e3008abda2b48ae0a808f9d2`.
The unchanged foundation is `SourceCurrentRequiredExposureSafe.lean`, SHA256
`2a70a36448950a7f490f64b671a4edae3014b15d82e0276de26d5a490e5b1e14`.

The mutual proof covers actual `RequireNode`, `RequireChildren`, and
`RequireRows` graphs. Its initial premises are semantic readiness, cost
history, physical availability or residency, causal `GuardHeap Plain`, and
`ExposureSafe`. It requires no global plain heap, finite Cap, result origin,
or future resource bound. It verifies a completed graph. It does not produce
completion.

`ExposureSafe.identity` permits any input for an empty requirement.
`ordinary` checks only selected existing children. Other children remain
unrestricted. `accepted` uses the actual source `unconstrained` predicate.
It does not infer this predicate from mere closure or depth zero.

`Origin` separates unchanged subtrees, plain returned regions, and ordinary
reconstruction. Each output row has an explicit original row index. Its full
guard and symbol remain equal, and its arity remains equal. Child origins
retain their ordered child positions. Node normalization can remove or
reorder rows. The row map need not be injective or order preserving.
Actual coherent constructor readback proves these facts for warm winners.

`RowAt` distinguishes ordinary row/child positions, union member indices,
and semantic stored Mu bodies. It excludes both Mu probes. The projection
`Origin.nonplain` gives an original occurrence for every addressed returned
nonplain row. `Origin.physical_positive` derives the same result when the
actual physical own-equality payload differs from `ok (some [])`.

The source-built integration constructs a nested constrained finite node,
a productive plain Mu, and an unselected constrained Mu. It computes its
own successful Required worker run and derives the actual graph. It proves
a nested returned positive-row occurrence and obtains its original source
occurrence through the new theorem. It also checks the exact unchanged
unselected Mu. The selected productive Mu executes actual exposure; no
completed graph or result law is a caller premise. This fixture is closed.
The public theorem retains the broader local safety domain.

Final checks: foundation direct1 and main direct6 have empty strict logs.
Canonical targets pass at 1080 and 1131 jobs under 4 GiB Max/High and zero
swap. Their logs replay one pre-existing ClosedCompletion warning.
Public2 checks and prints all 34 targets: 16 handwritten heads and 18
constructors. Kernel4 adds one constructed integration. Both printer logs
have no diagnostics and use only propext, Classical.choice, and Quot.sound.
The separate integration strict1 log is empty.

All six production attempts remain. Direct4 passed before occurrence
projection was added. Direct5 exited zero with unused-instance warnings;
it is not a clean final check. All four integration attempts remain.
Public1 failed before Lean because the sandbox could not access the user
bus. Public2 uses the authorized capped scope and succeeds.

The resumed peak recorder appended to an old WIP-pinned file. The full
appended bytes were preserved separately, and the original path was
restored to its exact old bytes. All 14 old manifest entries verify at their
original paths. The recovery, initial resolution, and final restoration
records remain separate. New checks use a new peak recorder path.

The initial false-primary producer is a separate component. The causal
union-normality requirement belongs there. These results do not prove an
origin-stratified decreasing rank, general outer progress, divergence,
or a Haskell defect or end-to-end correspondence.
