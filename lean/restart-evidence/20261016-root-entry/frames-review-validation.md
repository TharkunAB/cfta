# Independent active-frame validation

Validated at 2026-10-16 15:12 CEST.

Direct imported commands from `/home/tritlo/Code/mcfta`:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-root-entry/frames-review-public.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-root-entry/frames-review-kernels.lean
```

Final direct exit codes: 0 and 0. Public checks: twelve axiom reports and full signatures, plus the structure signature. Integration checks: four kernels and their axiom reports. Neither final log contains a warning, error, or `sorryAx`. All reported axioms belong to `propext`, `Classical.choice`, and `Quot.sound`. `frames-review-results.json` records actual direct exit codes and report counts.

Root-owned `frames-build-1.log` records canonical success in 1398 jobs. Root-owned `audit-build-2.log` records aggregate success in 2480 jobs and 58830 theorem dependency checks. Only the historical dependency warning occurs in those builds. The reviewer ran no Lake or Haskell build and changed no source proof, root document, Git state, or older evidence. Only new `frames-review*` evidence was written. No owned process or build slot remains active.
