# Literal parent and mutual outer checkpoint validation

Source main is `c0cc8a05`, merged at `896b0a1c`. The preceding published
checkpoint is `ade9584d`. Seven additive proof modules retain the optimized
interned core and all older proof sources. No Haskell file changes.

## Canonical builds

Root observed terminal exit 0 for every canonical process:

| Target | Jobs | Log |
| --- | ---: | --- |
| ParentWorker | 1407 | parent-worker-build-1.log |
| Parent Completion and Stability | 1458 | parent-completion-stability-build-1.log |
| Parent Actual | 1476 | parent-actual-build-1.log |
| PartialWorker | 1412 | partial-worker-build-1.log |
| Partial Completion and Stability, final | 1461 | partial-completion-stability-build-1.log |
| Complete Audit | 2471 | audit-build-1.log |

The complete Audit checks dependencies of 58623 MicroCFTA theorems.
Only propext, Classical.choice, and Quot.sound are permitted foundations.
The final builds contain only the historical unused-input dependency warning.
The first parent and partial-stability builds preserve new linter warnings
that were corrected before the final combined builds. No older source changed.
All process handles reached a terminal result. No canonical build is pending.

## Public declarations and integration checks

| Proof group | Public declaration checks | Integration kernels |
| --- | ---: | ---: |
| Parent definition | 4 | 7 |
| Parent Completion and Stability | 6 | 9 |
| Parent Actual | 8 | 6 |
| Outer definition | 10 | 12 |
| Outer Completion | 9 | 11 |
| Outer Stability | 17 | 9 |

All final focused checks pass. Imported final probes contain no errors,
new warnings, or sorryAx. Public checks include full signatures and axiom
reports. Parent Actual and both completion/stability groups retain their
own validation and hash manifests. Independent definition reviews retain
their source snapshots, public probes, kernel checks, and checksum files.
`final-evidence-checks.json` verifies every entry in those six manifests.
Earlier failed draft logs remain historical evidence. They are not final
validation results.

The kernels cover actual stored owners and selected finish handles,
zero-bound hits, untouched body paths, actual raw rejection sentinels,
literal Mu success and pending heaps, prefix error and missing states,
contradiction without child calls, returned-edge descendants, ordered
suffixes, current-state indexed descent, incomparable successful bounds,
and a next native query from the derived parent return.

## Preservation and source validation

`verify-preservation.py --require-current` passes. It checks all 5383
starting files and all 2463 older non-Audit proof sources. It permits only
the seven restart authorities and the three additive Audit imports to
change. All 234 starting Haskell files and all 206 active package files
retain their bytes. Twenty-eight frozen manifests check 228 module entries.
The historical repair block, current field-pool repair status, stashes,
and the three other worktrees remain. Earlier unavailable external drafts
are not claimed recovered. Root FINDINGS.md keeps the Haskell handoff first.

The unchanged source reuses its passing strict Nix build, 798 examples plus
golden, six-file Fourmolu, and four-package Cabal-gild and metadata checks.
Read source-validation-reuse.md. The historical Chain reproducer retains
its bytes and now returns FieldAtomOnDatatype. No extra source repair is
introduced or claimed.

## Scope

Parent Actual derives its own stable execution, strict Reads, language
Receipt, and full caller Post. The complete outer definition and finite
graph realizability now exist. Successful stability and uniqueness cover
all eight outer families and the complete caller state.

The outer worker still needs its same-success graph and strict-read Actual
adapter. General constrained outer completion, unequal-length classes,
repeated-pass convergence, host demand/publication, the noConstraint CAF,
and concrete runtime/frontend/query transfers remain open. The full-library
objective remains active. Read outer-actual-next.md and the current scope
note. This checkpoint establishes progress, not whole-library verification.
