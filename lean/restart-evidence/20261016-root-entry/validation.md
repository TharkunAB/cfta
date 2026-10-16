# Constructed root and active-owner checkpoint validation

## Objective and source refresh

The full objective remains implementation correspondence for the current
library. Languages, exact size classes, finite execution, counts, ordered
ranks and both inverses, probability laws, and transformations remain
separate contracts. This checkpoint makes progress. It does not complete
the full objective.

The starting published head is `a3b275f3`. The clean tracked checkout was
snapshotted before the opening bounded `git pull --ff-only`. Root observed
terminal exit 0 on process 26736. The pull reported `Already up to date.`
Source main remains `c0cc8a05`, merged at `896b0a1c`.
The backup is `backup/formalize-before-root-entry-20261016-1457`.
All older proofs, counterexamples, repairs, marked drafts, and the optimized
interned core remain. No Haskell implementation or production test changes.

## Canonical checks

Root observed terminal exit 0 for every canonical process. Only one Lake
process ran at a time. Direct imported Lean checks used the existing build
directory and did not take the canonical build slot.

| Target | Process | Jobs | Log |
| --- | ---: | ---: | --- |
| PartialInitialization | 51727 | 1329 | init-build-1.log |
| PartialConstructedRoot | 97986 | 1494 | root-build-1.log |
| PartialActiveOrder | 96956 | 1397 | progress-build-1.log |
| LocalPlain | 95914 | 1416 | localplain-build-1.log |
| PartialActiveFrames | 15216 | 1398 | frames-build-1.log |
| Audit after constructed entry | 96409 | 2477 | audit-build-1.log |
| Final Audit with all five modules | 89309 | 2480 | audit-build-2.log |

The final Audit checks dependencies of 58830 MicroCFTA theorems. Only
propext, Classical.choice, and Quot.sound are permitted foundations.
The historical unused-input warning remains. No new warning remains.
No canonical process is pending. The exact five module source hashes are
in frozen-modules.json. Audit.lean adds only the four current imports.

The pinned command is:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

## Imported public and integration checks

| Proof group | Public checks | Integration kernels |
| --- | --- | ---: |
| Initialization | 6 theorem pairs and 6 definition signatures | 6 |
| Constructed root | 2 theorem pairs | 4 |
| Active order | 29 declaration pairs | 10 |
| Current empty-own local worker | 6 theorem pairs and 1 definition signature | 6 |
| Completed active frames | 12 theorem pairs | 4 |

Each pair checks the full imported signature and its axiom dependencies.
Every final imported run returns exit 0 without warning, error, or sorryAx.
Each group retains its manifest, source snapshots, probes, logs, and review
or validation. Earlier failed draft logs remain historical evidence.
They do not describe the final source state.

Initialization kernels derive actual final-cache field loads, first owner
publication and Sound, retained table and issued histories, a valid existing
empty identity 37, generic unchanged canonical hits, and the computed input
model's validity. Root kernels derive all same-return Post and memo facts,
retain the actual preparation cache, and reuse the computed warm context
for a second root. A concrete empty root completes at all-zero bounds
without a supplied success or graph premise.

Active-order kernels check actual node-to-edge rank push, fresh indexed
descent with arbitrary inherited allocation, both finish families, structural
returned-child bounds, coherent key aliases, and lower warm-state retention.
Active-frame kernels check arbitrary excluded handles after literal success,
actual owner restoration, smaller-rank recursion, and ancestor restoration
before the next row suffix. Forward cell survival uses its separate protocol
frame. Reverse NoNewActive does not assert survival of every earlier cell.

Local kernels derive zero-bound completion from actual resident field loads,
retain exact native state and operation return, retain fourth and merge
memos, exclude every failed outcome, and handle an unresolved-reference
forest without traversing it. The effective own accessor includes positive
guard extraction. Empty stored payload alone does not imply its premise.

## Preservation and Haskell handoff

verify-preservation.py --require-current passes. The baseline contains 5561
tracked files and 2474 older non-Audit Lean sources. All older proof bytes
remain. Only the seven restart authorities and additive Audit imports may
change. Thirty frozen manifests check 237 module entries.

All 234 starting Haskell files and all 206 active package files retain their
bytes. Stashes and the three other worktrees remain. The six historical
repair entries and earlier PR #55 handoff text remain unchanged. The current
field-pool repair `b9219b9e` remains recorded first in root FINDINGS.md.
No new Haskell defect or repair was found in this checkpoint.

The unchanged Haskell source reuses the strict Nix all-component build,
798 examples plus golden, six-file Fourmolu, and four-package Cabal-gild
and metadata checks in the preceding drawn-fields-local-worker evidence.
The preserved Chain reproducer rejects the invalid derivation configuration
with `FieldAtomOnDatatype "Next" 0`. Standalone holds still treats pool
descendants as opaque. No source behavior repair is pending locally.

## Exact progress and remaining scope

Covered construction now derives initial Context, the singleton inventory,
and readiness of the actual empty inherited value. The constructed root
then derives its own graph, strict Reads, reached Checks, computed next
inventory, full Post, output support, and exact language law from literal
successful worker execution. Ordered field preparation can derive its own
causal History and actual returned interner.

Actual active-owner ranks, begin exclusion, push, finish, and completed
reverse frames provide current progress prerequisites. Empty effective own
equalities derive current local completion and original-or-erased child
shape at all bounds. No historical execution graph is transferred.

The next step derives current parent height and structural support before
constructing outer completion on the plain Region domain. This intermediate
domain does not replace general constrained completion. Unequal-length
classes, repeated-pass convergence, concrete shared-cache initialization,
GHC demand and publication, machine containers and identities, frontends,
generators, separate Sized/rank/probability contracts, solvers, random sources,
callbacks, codecs, full-pipeline composition, and older constructor/equality
work remain in scope. The full goal remains active.
