# Causal admission checkpoint validation

Source main is `8f85ddb605327bd088aae970ab058137c4f6d762`.
The starting formalize checkpoint is `6ba5d18b74f2b4322f134bb5a6332aa0e800c278`.
The opening `git pull --ff-only` completed with no changes.
The new proof commits are `f2e119b9`, `4b1d8e25`, and `49184f18`.
Audit and scope note commit is `ff561e50`.
No Haskell implementation or test files change.

## Canonical Lean validation

The pinned Lean 4.34.1 `lake build MicroCFTA.Audit` passes with exit code zero.
It completes 2320 jobs and checks dependencies of 56321 theorems.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Only the preexisting unused-input warning occurs. The terminal log is
`audit.log`. Focused builds also pass for all nine additive modules.

Separate public axiom reports, full signatures, and kernel integrations
cover each module. Pair admission probes construct actual canonical domain
entries, preserve older seen pairs, and inspect the literal returned cache.
Request probes cover actual joined-row membership, zipped children, Mu
entry, and grown-heap binder reads. Cache probes cover every stored phase,
actual lookup/demand/finish, both weaker invariants, and cross-view rebasing.
Node and edge probes compose the actual source certificates with protected
finish frames and literal emitted checked-edge branches.

| Module | Public axiom reports | Public signatures | Kernel integrations |
| --- | ---: | ---: | ---: |
| PairAdmission | 12 | 12 | 12 |
| RequestAdmission | 14 | 14 | 4 |
| AdmissionCache | 18 | 22 | 12 |
| AdmissionExecution | 4 | 6 | 2 |
| AdmissionCode | 4 | 5 | 2 |
| AdmissionNodeCertificates | 7 | 7 | 3 |
| AdmissionEdgeCertificates | 3 | 3 | 7 |
| AdmissionTrace | 3 | 5 | 1 |
| CoveredQuery | 3 | 4 | 3 |
| Total | 68 | 78 | 46 |

Eight kernel integrations are named theorems. Their eight additional axiom
reports contain only the permitted foundations. Eight additional signature
checks cover these kernels. Earlier failed evidence
elaboration logs remain; their temporary error placeholders do not occur
in the final probe or any proof source.

Root execution and trace checks retain the whole returned state. The query
checks derive actual completion, closed resident output, exact physical
intersection language, all-phase Covered, returned Admitted, and seen-pair
admission. The generated endpoint exposes the literal expanded inventory.
Its per-query result does not require a future admission or result-law oracle.
Independent reviews found no material semantic defect.

The two-generated-query kernel completes the first call and uses its
actual returned value as the next left operand. The first receipt supplies
every second-call cache invariant, physical fact, closedness fact, and
source growth/history. Only the next reached WordRanges is new. The second
result retains coverage and exactly the original intersection language.

The initial warm entry still supplies Good, Contextual, all-phase Covered,
Scoped, SemanticReady, Idle, source growth/history, operand facts, and
reached WordRanges. Empty modeled native tables derive initial Covered.
The complete generated history and source seeded fold remain composition
obligations. No GHC global cache reset is claimed.

Saved failed logs remain. Root corrections qualify the checked `execute`
in simplification, retain the correct binder after equality substitution,
project yielded Fields from OutcomeFields, use the actual body readiness
field, and state the exact demand-machine equality before transitivity.
The final sources and terminal build pass. No placeholder or project axiom
was introduced to resolve these failures.

## Haskell validation and external handoff

`git diff --exit-code 6ba5d18b -- cfta cfta-generator cfta-ghc decision-model`
passes with no output. Reuse the unchanged-source strict Nix all-component
build, 777 examples plus golden, five-file Fourmolu, and four-package
Cabal-gild results from the source refresh.

The diff against source main retains only the historical fresh-probe
changelog entry and the equality-endpoint reproducer comment. It contains
no outstanding behavior patch. The complete external repair registry
remains at the top of root FINDINGS.md. Every later Haskell fix must record
its failure case, affected files, commit, checks, and upstream status there.

## Preservation and remaining scope

The starting inventory contains 3538 files. None is missing.
All 2310 older non-Audit proof sources retain identical bytes. The only
changed starting files are the seven restart documents and additive Audit
imports. All eleven preceding frozen manifests and the current nine-module
manifest pass. Stashes, other worktree records, and the Haskell registry
remain unchanged. Read `preservation-final.json` and `frozen-modules.json`.
Earlier external draft bytes were unavailable before this checkpoint.
No recovery or reverification is claimed.

Scoped source/documentation `git diff --check` passes. Raw saved logs can
contain whitespace in Lean diagnostic output. The complete source and log
manifest is repository-local. Temporary compiled olean output is excluded.

Next carry the actual expanded inventory and coverage through the complete
seeded fold, then prove common-subtree inclusion, the checked class witness,
current stopped-class soundness, and the general constrained outer caller.
Every other full-library and separate Sized contract remains active.
Read `lean/notes-current-native-admission-history.md` for the exact scope.
