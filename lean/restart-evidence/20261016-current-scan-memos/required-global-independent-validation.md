# Independent validation

Date: 2026-10-16 08:27 CEST.

No Lake build was run. Parent-reported focused builds were already terminal green: RequiredGlobalMemos 1284 jobs; AllocatedRequired 1348 jobs. This review does not rerun or independently certify those job totals.

Pinned commands run directly against existing compiled dependencies:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-current-scan-memos/required-global-independent-public.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-current-scan-memos/required-global-independent-kernels.lean
```

Results:

- Three public theorem axiom reports: PASS, exit 0. Only propext, Classical.choice, and Quot.sound occur.
- Three public theorem signature checks: PASS in the same direct run.
- Five kernel compositions: PASS, exit 0, no warnings, final log `required-global-independent-kernels-2.log`.

The five kernels check: derived exact native/domain/equality state retention with ScanReads and final global validity; literal required completion with independent exact filter language; positional selected-record path domains; two equal-path original occurrences retained in literal source order; and constructed entry with empty fourth memo deriving a current Scan and finite required continuation on success. The final kernel has no completed Scan/required-worker premise.

The first kernel run failed only because the new evidence file omitted existential type annotations and explicit implicit primary-trace arguments. Its raw log is retained as `required-global-independent-kernels-1.log`. Only the evidence file was corrected. The frozen proof sources were not changed.

Frozen source copies, raw logs, review, probe source, and this report are covered by `required-global-independent-SHA256SUMS`.
