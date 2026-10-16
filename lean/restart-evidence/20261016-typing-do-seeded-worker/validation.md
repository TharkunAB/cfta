# Literal seeded and current Scan checkpoint validation

Previous goal turn: PROGRESS. Current goal turn: PROGRESS. The full library
objective remains active. This checkpoint does not complete that objective.

## Source refresh

The opening bounded pull of formalize completed with exit zero and reported
up to date. The bounded fetch of main completed with exit zero. Source main
`5399d310` is merged at `82d47236`, after published head `e75e8c5c`.
The backup branch is
`backup/formalize-before-main-5399d310-20261016-1316`.

PR #63 adds qualified typing do-notation in five generator paths. Three are
Haskell files, including the new Typing/Do.hs. The core, equality operations,
Sized, GHC package, decision model, and prior Lean sources do not change
upstream. No local Haskell repair is made. Root FINDINGS.md keeps all six
prior repair/counterexample entries and the PR #55 handoff intact. The
recursive field-pool contract gap remains confirmed and unfixed.

`source-validation.md` records the current strict Nix all-component build
with tests and benchmarks enabled and `-Werror`. It exits zero. All six
suites exit zero: 793 examples with zero failures, plus the golden check.
Counts: 321 core, 240 generator, 175 refinement, 35 GHC-fit, and 22 decision
model examples. Fourmolu passes on three Haskell files. Cabal-gild and
metadata checks pass on all four active packages. No hoogleplus recovery
was needed. The old dynamic-symbol linker warning remains. The sole
Haskell slot was released after the actual suite process terminated.

The do-notation review records ordinary list order and duplicate choices,
dependent choices, false guards, and failed patterns. It does not prove
compiler desugaring, arbitrary custom codecs, or infinite-list completion.
The prior typing builder implementation is unchanged except documentation.
The earlier 791-example result is not reused for this new source.

## Proof checks

Twelve new modules implement literal seeded queries, current gate wrappers,
and Scan with full caller receipts. Proof commits are `8978d180`, `19f90e9c`,
and `2b26e442`. Audit and scope note are committed at `36d04e62`. The seven
restart authorities are updated at `81de71ce`.

Pinned Lean 4.34.1 completes the full Audit with terminal exit zero: 2456
jobs and 58268 theorem dependency checks. Tool session 27324 was polled to
that terminal result. `audit.log` records it. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. The old unused `inputs`
warning remains. No new warning or forbidden dependency is accepted.

Every canonical process was root-managed and polled to terminal. No two
canonical Lake processes ran together. Final focused builds all pass:
Caller 1270, Worker 1185, Completion 1186, Stability 1190, seeded Actual
1278, Gate/Scan 1197, ScanCaller 1279, ScanStability 1286, and ScanActual
1297 jobs. Final public probes and integration kernels pass. Draft failures
remain in the raw logs. Earlier missing-oLean probes do not count as passing
validation; corrected final checks and the complete Audit do.

Independent source reviews find no material defect. The root seeded Caller
and WorkerActual are reviewed against their exact source hashes. The Scan
definition is checked against primary selection, secondary skipping,
current memo calls, failure state retention, and lazy suffix boundaries.
The root Scan Caller/Actual review verifies same-return strict Reads,
computed inventory, full Context/Post, original availability, and conditional
stopped-class exclusion. A separate alignment review checks the complete
Result pair, checked state, and fourth memo.

Integration kernels derive a second literal call's Context and At from the
first computed inventory. Other kernels derive the supplied success's own
strict reads, stopped original-class refutation, a generated follow-up
native query, zero-bound warm hits, early stop before arbitrary suffixes,
incomparable successful bounds, and exact failed selected prefixes.
`artifact-manifest-check.json` checks all entries in the five JSON manifests.
The source, gate, and Scan caller SHA256 manifests also pass individually.

## Preservation

`verify-preservation.py --require-current` checks all 5135 starting tracked
files. None is missing. All 2443 older non-Audit Lean sources retain their
bytes. Only the seven restart authorities, Audit's two additive imports,
and the five exact upstream paths may change. Active package membership
adds exactly Typing/Do.hs. There is no local Haskell behavior patch.
Twenty-six frozen manifests check 213 module entries, including all twelve
new modules. The historical repair/counterexample block and PR #55 handoff
remain byte-identical. Stashes and the three other worktree records remain.

The raw starting-worktrees.txt retains its final blank separator. Exclude
that raw capture, command logs, and raw source patches from source whitespace
checks. The historical WORK-IN-PROGRESS.md and scan-worker.DRAFT.md remain
as timed development records. The final proof state is described here and
in the new scope note. No failed draft or earlier evidence is deleted.
Unavailable earlier external drafts are not claimed recovered.

## Scope and next work

Finite literal Seeded and Scan execution now comes from legitimate initial
facts and reached word checks. No future graph, body law, arbitrary gate
answer, or final invariant is a public premise. Seeded language preserves
common selected subtrees. A stopped Scan result excludes its original class
on accepted original forests. Only a no-stop completion reads the full
class partition; a stopped Scan retains its reached selected prefix.

Serial execution graphs and logical global read receipts do not establish
concrete GHC demand, memo publication, host table events, or the
noConstraint CAF. General constrained outer termination remains open.
The current root_exact theorem assumes a completed strict-read outer call.

Read `local-worker-next.md` and `lean/notes-current-scan-worker.md`. Next
compose local precheck/reduction, required children, and class passes, then
parent construction and the mutual outer worker. Keep unequal-length path
classes, repeated-pass convergence, frontend and generator adapters, exact
Sized and probability contracts, solver IO, random draws, callbacks, codecs,
concrete runtime, and older constructor/equality targets active. Preserve
the optimized interned core. Record every Haskell repair first in root
FINDINGS.md. Push verified formalize checkpoints regularly. No board posts
or deployments. Keep the full objective active.
