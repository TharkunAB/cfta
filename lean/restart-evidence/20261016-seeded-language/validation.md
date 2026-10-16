# Seeded language and sound allocated Scan validation

Source main is `8f85ddb605327bd088aae970ab058137c4f6d762`.
Starting formalize checkpoint is `34066d332aa9ca58ab62c7d0479946330c84976f`.
The opening git pull --ff-only completed with no changes.
Proof commits are `20a9336e` and `57ead43f`.
Audit and scope note commit is `37aa70c8`.
Restart document commit is `65de87a5`.
No Haskell implementation or test file changes.

## Canonical Lean validation

The pinned Lean 4.34.1 lake build MicroCFTA.Audit passes with terminal
exit code zero. It completes 2327 jobs and checks dependencies of 56369
theorems. Only propext, Classical.choice, and Quot.sound are permitted.
Only the preexisting unused-input warning occurs. Raw log: audit.log.
Focused canonical builds pass for all seven additive modules.

Public axiom reports, complete signatures, and kernel integrations pass:

| Module family | Public axiom reports | Public signatures | Kernel integrations |
| --- | ---: | ---: | ---: |
| InventoryState | 4 | 7 | 4 |
| SeededOperandLanguage | 2 | 2 | 6 |
| SeededLanguage | 5 | 7 | 5 |
| ClassWitness, RefusedClassQuery, ClassScanSoundness | 9 | 9 | 9 |
| AllocatedScanSoundness | 2 | 3 | 3 |
| Total | 22 | 28 | 27 |

Named integration kernels also have independent axiom and signature checks.
Every reported axiom set uses only the three permitted foundations.
Final direct probes have no warnings, errors, or sorryAx.

The integrations retain literal empty-seed behavior, two- and three-path
source projection order, inner and outer checked native traces, exact
full-state uniqueness, and a whole seeded fold followed by another generated
query. The latter uses its actual final result as both next operands and
adds only the next reached WordRanges. An earlier two-generated-query
kernel retains a distinct right operand in the admission-history evidence.

Class kernels derive common proper subtrees and exact source seed rotation.
Current memo hit and miss kernels derive original class refutation.
Scan kernels expose final inventory At, physical readiness, fourth-memo
retention, and rejection of the original complete constraint conjunction.
Constructed-entry kernels derive the initial fourth-memo Correct from
empty tables. They retain the actual precheck native machine, both cold
native tables, and the literal returned equality operations. The finite
endpoint derives actual Scan, final At, and rejection of any returned class.

Independent source reviews are seeded-root-review.md and
allocated-scan-root-review.md. Neither found a material defect. The source
order, actual current conjunction memo, open unrelated siblings, and the
initial warm versus constructed cold boundaries are reviewed explicitly.

Raw failed logs remain. The root fold's first elaboration supplied one
extra constructor alternative binder. The allocated entry's first two
elaborations used an unparenthesized proof-field literal and a source
notation that conflicted with a structure field. The final sources use
the actual constructor arity and an unambiguous structure declaration.
No placeholder, project axiom, or weakened result resolved those failures.

## Haskell validation and external handoff

Git diff --exit-code 34066d33 -- cfta cfta-generator cfta-ghc decision-model
passes with no output. Reuse the unchanged-source strict Nix all-component
build, 777 examples plus golden, five-file Fourmolu, and four-package
Cabal-gild evidence from the source refresh. No local test file changes.

The comparison with source main retains only the historical fresh-probe
changelog entry and the equality-endpoint reproducer comment. It contains
no outstanding behavior patch. The external repair registry remains first
in root FINDINGS.md and retains its previous bytes. Every later Haskell fix
must record the failure case, affected files, commit, checks, and upstream
status there.

## Preservation and remaining scope

All 3638 starting files remain. All 2319 older non-Audit proof sources retain
identical bytes. Only the seven restart documents and additive Audit imports
change among those starting files. Thirteen frozen manifests pass, including
the current seven-module manifest. Stashes and other worktree records are
unchanged. The root Haskell fix registry is preserved.
Read preservation-final.json, frozen-modules.json, and verify-preservation.py.
Earlier unavailable external drafts are not claimed recovered or reverified.

Scoped source/documentation git diff --check passes. Raw saved logs can
contain whitespace from diagnostics. The complete evidence checksum manifest
is repository-local. No derived olean, ilean, object, or generated C artifact
is included.

The complete checked seeded fold, current class witness, original stopped
Scan refutation, and constructed allocated finite Scan with final inventory
are now proved under the stated source and reached-range contracts.
Initial At remains explicit only for a general warm entry. The constructed
endpoint derives At from its literal cold native tables. No global GHC
cache reset is claimed. No completed native query or final-law oracle is a
premise of the constructed finite endpoint.

Next compose all three global gate memo receipts with the CURRENT checked
Scan, selected required paths and later edits, then the general constrained
outer caller. Every other full-library and separate Sized contract stays
active. The exact explicit-map Sized algorithmic contract is already proved.
Runtime-family wiring, newer frontend adapters, concrete containers, GHC
forcing and memo publication, allocation order, concurrency, machine ranges,
solver IO, random draws, and codecs retain explicit boundaries.
The full goal remains active. This checkpoint is verified progress.
