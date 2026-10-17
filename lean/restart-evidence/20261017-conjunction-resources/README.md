# Initial conjunction numeric checkpoint

Updated: 2026-10-17 13:40 CEST. Starting checkpoint: 2d7b0fa2.
Source proof commit: 75348c57. Source main: c0cc8a05, merge 896b0a1c.
Read ../../notes-current-conjunction-numeric.md for contracts and open work.

The complete public Haskell theorem remains open. The current producer
constructs its own numeric conjunction call and full caller return.
AnswerSound is one-sided. False does not establish nonemptiness.
The bounds use the guard list at the memo entry heap. Whole-Scan guard
forecasting across native queries remains open.

## Production checks

Each strict check uses an immutable source snapshot. Its bytes equal the
final production source. Every final strict log is empty with exit 0.
Every canonical target passes. Read frozen-modules.json,
current-strict-logs.json, and build-logs.json for exact inputs.

| Module | Strict snapshot | Strict log | Canonical log |
| --- | --- | --- | --- |
| SourceCurrentConjunctionGuardUniverse | guard-universe-direct-2.source.lean | guard-universe-direct-2.log | guard-universe-canonical-1.log |
| SourceCurrentConjunctionTupleBounds | tuple-bounds-direct-3.source.lean | tuple-bounds-direct-3.log | tuple-bounds-canonical-1.log |
| SourceCurrentConjunctionProjectionResources | conjunction-projection-direct-5.source.lean | conjunction-projection-direct-5.log | conjunction-projection-canonical-1.log |
| SourceCurrentConjunctionExposureResources | exposure-direct-3.source.lean | exposure-direct-3.log | exposure-canonical-1.log |
| SourceCurrentConjunctionRequirementResources | requirements-direct-5.source.lean | requirements-direct-5.log | requirements-canonical-2.log |
| SourceCurrentConjunctionRequirementNumeric | requirement-numeric-direct-1.source.lean | requirement-numeric-direct-1.log | requirement-numeric-canonical-1.log |
| SourceCurrentConjunctionTupleNumeric | tuple-numeric-direct-2.source.lean | tuple-numeric-direct-2.log | tuple-numeric-canonical-1.log |
| SourceCurrentConjunctionRowsResources | rows-direct-3.source.lean | rows-direct-3.log | rows-canonical-2.log |
| SourceCurrentConjunctionWorklistResources | worklist-direct-2.source.lean | worklist-direct-2.log | worklist-canonical-1.log |
| SourceCurrentConjunctionGuard | conjunction-guard-direct-2.source.lean | conjunction-guard-direct-2.log | conjunction-guard-canonical-1.log |
| SourceCurrentConjunctionNumeric | numeric-direct-1.source.lean | numeric-direct-1.log | numeric-canonical-1.log |
| SourceCurrentConjunctionCallerNumeric | memo-frame-direct-1.source.lean | memo-frame-direct-1.log | memo-frame-canonical-1.log |

The pinned full Audit passes 2983 jobs and 65714 dependency checks.
The graph retains one earlier warning in unchanged
InternedFreshOrdinaryClosedCompletion. No new strict warning remains.
No sorryAx, new axiom, or linter disable is used.

## Independent checks

kernel-logs.json selects the exact successful sources and logs.
Seventeen groups check 116 distinct public declarations and fourteen
constructed integrations. Each has a complete signature and axiom report.
Only propext, Classical.choice, and Quot.sound occur.
Public probes print complete proof terms. The three exploration integrations
retain complete signatures and axiom reports without printing proof terms.
They construct their own Rows, Run, and Memo.Call from actual source input.
The caller integration constructs Context, Frame, and Fits from its own
source heap. It invokes the initial complete endpoint. It also constructs
an exact physical warm call from the produced installed entry. It does not
claim a separate warm worker execution.

The successful tuple-bounds kernel log has 52,698,409 raw bytes. Its gzip
archive preserves every byte. tuple-bounds-log-archive.json records raw and
compressed hashes. The component verifier decompresses and checks both.
No proof text or diagnostic is removed.

Nine component manifests retain 305 entries and 305 hash references.
Each of the eight independent component verifiers passes. The root
resources-manifest.json retains seven root producers and their attempts.
verify-checkpoint.py verifies all manifests, public coverage, successful
probe pairs, standard axioms, final strict snapshots, and canonical builds.
checkpoint-validation.json is its complete report.

## Earlier attempts and diagnostic provenance

Failed and intermediate production and kernel attempts retain their bytes.
Their diagnostics are not successful proof evidence. Requirements strict
attempt 4 and canonical 1 passed with a warning. Final attempt 5 and
canonical 2 are clean. Caller kernel attempt 4 was interrupted with exit
130 during large proof printing after its axiom reports. Attempt 5 passes.
Earlier partial exploration public checks are not counted again.

Two auxiliary instance-resolution commands did not create original raw log
files. Read conjunction-guard-diagnostic-provenance.md for the exact limit.
Its retained reconstructed scratch sources are not successful evidence.
All production, public, and kernel attempts have separate source snapshots
and raw logs. The checkpoint verifier's first attempt rejected the source
constructor name admit. Its saved script and reproduced diagnostic remain
in checkpoint-verifier-1.source.py and checkpoint-verifier-1.log. The final
verifier distinguishes that constructor from an admitted proof.

## Preservation and source validation

verify-preservation.py --require-current checks 15353 starting files,
2970 older non-Audit sources, 239 Haskell files, 206 active-package files,
both stashes, three other worktrees, and 95 frozen module manifests with
740 entries. Only seven restart authorities and twelve new Audit imports
change from the baseline. Earlier proofs and evidence retain their bytes.

This checkpoint adds no Haskell patch or new behavior defect. Root FINDINGS
keeps the external repair registry first. Field-pool repair b9219b9e is
merged in unchanged source c0cc8a05. The original Chain reproducer returns
Left (FieldAtomOnDatatype "Next" 0). Standalone holds remains opaque.
Reuse the strict Nix 798-example plus golden validation, Fourmolu checks,
and Cabal-gild checks in ../20261016-drawn-fields-local-worker/.

SHA256SUMS covers every file in this evidence directory except itself.
verify-closure.py checks every tracked file's bytes and mode against the
index and HEAD. It requires every checksum file to be tracked, the exact
checkpoint report, current preservation, and a clean tree. With
--remote-file, it also checks remote formalize equals HEAD and main equals
c0cc8a05. Closure output is kept in /tmp to retain the frozen checksums.
