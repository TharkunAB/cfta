# Shared and outer guard checkpoint

Validated: 2026-10-16 23:22 CEST.

This checkpoint makes proof progress. The full-library goal remains active.
The root's numeric capacity Plan and quantitative outer output certificates
remain open. Read `lean/notes-current-shared-guards.md` and
`next-quantitative-outer-producers.md` before continuing.

## Source and preservation

- Starting published formalize: 56edaf319fec1ace22d75b3e01edc5ace98d1d5f.
- Source main: c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e.
- Source merge: 896b0a1c. The starting pull reported already up to date.
- Backup branch: backup/formalize-before-shared-guards-20261016-2306.
- Proof commits: 35b7d962, d5fd539c, 9c1d3d38, 07607c71, ac44d4c5.
- Documentation commit: 32155be4.

The baseline hashes 8313 starting tracked files. Preservation retains all
2645 older non-Audit proof sources and all 234 Haskell files. The only older
file changes are seven restart authorities and twelve additive Audit imports.
The production registry checks 52 frozen manifests with 415 module entries.
Stashes and three other worktrees remain unchanged. Historical repair reports,
executable counterexamples, logs, and marked drafts retain their bytes.
Earlier unavailable external drafts have no recovery claim.

No Haskell behavior change or new defect is part of this checkpoint.
Root FINDINGS records upstream repair b9219b9e before historical reports.
The original Chain pool reproducer returns FieldAtomOnDatatype.
The unchanged source retains its strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild validation from the source refresh evidence.

## Validation

The pinned Lean Audit passes 2658 jobs and 61077 theorem dependency checks.
All 75 public axiom/full-signature pairs and 12 integration pairs pass.
Only propext, Classical.choice, and Quot.sound occur. Final strict checks
of all new production sources have no diagnostic. Earlier dependency linter
warnings replayed by Lake remain visible in the canonical logs.

The kernels cover actual target miss and slot publication, same-state warm
reuse, leaf query order, Empty callbacks, repeated positions under one common
guard vector, a constructed class pass, initial resident own precheck,
constructed parent resources, rejection without child demand, parent-to-outer
composition, and a whole-state outer warm hit. Both new root construction
endpoints have full explicit signatures and axiom reports. The reached Plan
remains visible in those signatures.

Eleven component and independent-review manifests verify 229 entries.
They require no historical input resolution. Review notes retain exact hashes.
Failed attempts retain raw sources and logs. The final public probes remove
unsupported pretty-print options. The final numeric proof fixes a local name
collision, unfolds the intended row definition, and scopes unused instances.
No failure artifact is substituted for a passing production check.

The numeric parent comparison bounds the existing deterministic selector.
It does not by itself derive profiles for every arbitrary completed parent.
Outer store retention proves universal lower native and Merge guard laws.
It does not add quantitative guard laws to outer returned cells. These
boundaries are required for the next proof target.

## Commands and frozen evidence

The pinned toolchain is leanprover--lean4---v4.34.1.
The canonical command is `lake -d lean build MicroCFTA.Audit` from the root.
Individual module and imported kernel logs are listed in the manifests.
`kernel-logs.json` identifies every final source, log, and expected pair count.
`frozen-modules.json` pins all twelve new production modules.

The checkpoint verifier checks source hashes, code placeholders after nested
comment removal, all printed axiom sets and signatures, canonical build logs,
and every component manifest. The preservation verifier checks the baseline,
all production registries, historical Haskell handoff, stashes, and worktrees.

Both verifiers write their JSON reports. Copy them into a new evidence
directory and adjust their inputs before running them in a later turn.
Do not rerun them in this frozen directory. SHA256SUMS pins every checkpoint
artifact except itself. Its content is frozen before the evidence commit.

General recursive progress, convergence, frontend and runtime correspondence,
and complete public pipelines remain open. Request counts do not prove
normalization, solver, runtime, or memory bounds.
