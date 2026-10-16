# Current plain parent and edge-call checkpoint

Validated on 2026-10-16. Starting published commit is `8906d5e6`.
Source main is `c0cc8a05`, merged at `896b0a1c`.
Backup branch is `backup/formalize-before-parent-plain-20261016-1517`.
The opening bounded pull completed with exit zero and no source change.

## Proof commits

- `db438c0b`: derive the full plain local range plan.
- `b7fd0ee5`: track structural support of returned edge owners.
- `3f817e89`: construct finite plain parent execution and child Shape.
- `96a1afee`: transport the plain domain through actual cached owners.
- `6bbf2ee0`: construct finite literal current plain edge calls.
- `967773de`: import the endpoint into Audit and record its proof boundary.
- `b447b763`: update all seven restart authorities and Haskell repair status.

## Canonical builds

The pinned toolchain is Lean 4.34.1. The build command is
`/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build TARGET`.
Only one canonical Lake process ran at a time.

| Target suffix | Log | Jobs | Observed process | Exit |
| --- | --- | ---: | ---: | ---: |
| SourceCurrentAllocatedLocalPlainRanges | localplain-ranges-build-1.log | 1489 | 24209 | 0 |
| SourceCurrentAllocatedPartialReturnedDomain | domain-build-1.log | 1403 | 62441 | 0 |
| SourceCurrentAllocatedParentPlain | parent-build-1.log | 1493 | 5422 | 0 |
| SourceCurrentAllocatedPartialPlainInputs | inputs-build-1.log | 1404 | 9225 | 0 |
| SourceCurrentAllocatedPartialPlainEdgeCall | edgecall-build-1.log | 1500 | 96376 | 0 |
| Audit | audit-build-1.log | 2485 | 68247 | 0 |

Audit checked 58868 theorem dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. The existing unused
`inputs` warning remains in `InternedFreshOrdinaryClosedCompletion`.
No new proof source changed after its final canonical build.
All listed processes were observed at terminal exit zero.

## Independent probes and review

Final imported probes contain 28 public axiom/signature pairs and 25
integration kernel pairs. All final direct runs exit zero. Their logs
contain no warning, error, or `sorryAx`. Draft failure logs remain as evidence.

The kernels cover full range derivation, same-return child Regions and
rank bounds, actual stored-owner transport, ready-cache whole-caller
identity, exact finish handles, successive calls at computed inventories,
raw rejection at zero bounds, open opaque terminals, and the nullary
singleton-Empty case. The independent EdgeCall review finds no circular
execution premise, owner mismatch, or state mismatch.

`verify-component-evidence.py` checks six component manifests, including
66 source and evidence entries. It also checks 40 entries in the three
component checksum files. Every hash matches. `component-verification.json`
records the exact manifests and final probe logs.

## Preservation

`verify-preservation.py --require-current` checks all 5648 starting tracked
files. All files remain. All 2479 older non-Audit proof sources retain their
bytes. Audit adds only the new endpoint import. The permitted changes to
older tracked files are Audit and the seven restart authorities.

Thirty-one frozen module manifests check 242 entries without a mismatch.
All 234 starting Haskell files and all 206 tracked active-package files
retain their bytes. Stashes and the three other worktrees remain unchanged.
The historical repair block from `e75e8c5c` retains its bytes. The external
Haskell repair registry remains the first section in root FINDINGS.md.

`source-working-diff.patch` records the unchanged historical differences
from source main: the constructor repair changelog and the outer-cycle
reproducer comment. This checkpoint adds no Haskell behavior change.
Reuse the strict Nix build, 798 examples plus golden, six-file Fourmolu,
and four-package Cabal-gild and metadata checks recorded in
`20261016-drawn-fields-local-worker` for the unchanged source.

`SHA256SUMS` freezes every file in this evidence directory except itself.
Do not run a script that rewrites an older frozen report.

## Remaining proof

The new finite theorem constructs the actual outer EdgeCall from initial
Context, inherited readiness, resident input, Plain, Stored, and active
order. Its result includes stable execution, its own graph, strict Reads,
Checks, full Post, residency, Stored, Shape, and EdgeLaw. No supplied
literal success, future body, range plan, or desired result law is needed.

The recursive node and descendant completion proof remains open. Read
`region-next-review.md` and `lean/notes-current-plain-edge-completion.md`.
The node-rank induction outline in the note has not been implemented.
General constrained termination, unequal-length path classes, repeated
passes, current frontend and runtime transfers, and full-pipeline
composition remain open. The full-library goal stays active.
