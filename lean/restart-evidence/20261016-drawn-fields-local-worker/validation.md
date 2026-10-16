# Current drawn-field refresh and literal local reduction validation

Previous goal turn: PROGRESS. Current goal turn: PROGRESS. The full library
objective remains active. This checkpoint does not complete that objective.

## Source

The opening bounded formalize pull exited zero and reported up to date.
The bounded main fetch exited zero. Source `c0cc8a05` is merged at
`896b0a1c`, after published checkpoint `66013b03`. Backup branch
`backup/formalize-before-main-c0cc8a05-20261016-1346` retains that checkpoint.
The seven-file delta adds drawn typing fields and the FieldAtomOnDatatype
repair. No additional local Haskell behavior patch is made.

The sole Haskell owner observed strict build handle 68327, test handle
35230, and preserved-reproducer handle 60585 to terminal exit zero. The
slot was then released. All components build in Nix with -Werror, tests,
and benchmarks enabled. Six suites pass: 321 core, 240 generator,
180 refinement, 35 GHC-fit, and 22 decision-model examples, plus golden.
This is 798 examples with zero failures plus the golden check. Fourmolu
checks six incoming Haskell files. Cabal-gild and metadata checks pass on
all four active packages. The old dynamic-symbol linker warning remains.
No hoogleplus installed-unit recovery was needed.

The historical Chain reproducer retains SHA256
`aca168328f288fedf671fc30a535bf5d4643aeaed1662f3bd214936f663ee8ac`.
It now reports `Left (FieldAtomOnDatatype "Next" 0)` instead of returning a
generator with Next (End False). The standalone holds checks still report
`(True,True,False)`. The repair rejects an invalid derivation configuration;
it does not recursively validate opaque supplied pools. Root FINDINGS.md
records the repair, local merge, files, reproducer, and actual checks first.
The six historical entries and PR #55 handoff retain their original bytes.

`source-validation.md` and raw logs record exact commands and results.
The drawn-field tests verify symbolic million-value counting, finite-pool
language agreement, invariant filtering/count agreement, and plain-builder
DrawnField rejection. No Lean frontend adapter or shared rank-order theorem
is inferred from those tests. typingLTA uses its generator order.

## Proofs

Eight additive modules are committed in three focused changes:

- `7f9db45e`: original-record Scan, success stability, and full actual caller.
- `ececc503`: unconditional successful required-worker bound stability.
- `9e3f6174`: literal local worker, stable completion, success stability and
  uniqueness, and full caller adapter at its computed inventory.

Audit and scope note are committed at `01c36d68`. The seven restart
authorities and current external repair status are committed at `6c7b0569`.

The root managed every canonical Lake process and observed terminal results.
No canonical Lake processes overlapped. Final canonical checks pass:
record/local worker 1424 jobs (6850), record Actual 1320 (12047), required
and local stability 1434 (41118 final), local completion 1445 (79054),
and local Actual 1466 (97225). The full Audit handle 78515 exits zero:
2464 jobs and 58403 theorem dependency checks. Only propext,
Classical.choice, and Quot.sound are permitted. Only the old unused-input
warning remains. Earlier raw parse/probe failures and the corrected unused
section warning remain in their historical logs; none counts as final success.

All public and integration checks pass with exact frozen source hashes:

| Check | Public axiom/signature pairs | Integration kernels |
| --- | --- | --- |
| Record Scan and stability | 10 declarations | 8 |
| Record Actual | 4 | 6 |
| Required stability | 11 | 6 |
| Independent local worker and stability review | 14 | 7 |
| Local Actual | 3 | 6 |
| Independent local completion review | 3 | 5 |
| Independent local Actual review | 3 | 3 |

Independent reviews find no material defect. Kernels include equal-path
records retaining both original occurrences, selected prefixes before stop,
stopped suffixes with zero continuation bounds, exact pending/failed states,
complete class-local slot diagnostics, arbitrary larger bounds, and full
return uniqueness. Successive literal calls derive the second Context and
At from the first computed inventory. Another kernel starts a generated
native query from a supplied local return using its derived physical facts
and only the next reached word ranges. No future body law is supplied.

`artifact-manifest-check.json` verifies all entries in six JSON manifests.
The source-validation and local-review SHA256 manifests pass individually.
`frozen-modules.json` retains all eight final module hashes.

## Preservation and remaining scope

`verify-preservation.py --require-current` passes. All 5274 starting tracked
files remain. All 2455 older non-Audit proof sources retain their bytes.
Only the seven restart authorities, one additive Audit import, and the seven
exact upstream paths may change. All seven upstream files match source
`c0cc8a05`. Active package membership is unchanged. No unrelated source patch
is introduced. Twenty-seven frozen manifests check 221 module entries.
Stashes and three other worktree records retain their starting values.
All prior raw evidence, marked drafts, counterexamples, and historical
pending notes remain. Earlier unavailable external drafts are not claimed
recovered. Exclude starting-worktrees.txt's raw final separator and command
logs from source whitespace checks.

The local caller theorem derives stable execution and the same actual
strict reads, language receipt, final probes, and full Post at its computed
inventory from legitimate initial Context, actual stored-field load,
inherited readiness, residency, and reached range plans. No completed future
graph, body law, or final invariant is a public premise. Its language law
is unconditional narrowing and guard/inherited conditional equivalence.
Serial logical execution does not prove GHC demand, host table events,
lazy publication, or the noConstraint CAF.

Read parent-worker-next.md and lean/notes-current-local-worker.md. Next
implement literal parent construction, then the eight mutual outer worker
families. Raw rejection must precede field lookup and child work. General
constrained outer termination, unequal-length path classes, repeated-pass
convergence, runtime/frontend/public API adapters, exact Sized and probability
contracts, solver IO, random sources, callbacks, codecs, full pipeline
composition, and older constructor/equality work remain active. Preserve
the optimized interned core. Record each Haskell repair first in root
FINDINGS.md. Push verified formalize checkpoints regularly. No board posts
or deployments. Keep the full objective active.
