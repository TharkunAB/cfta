# Independent returned-domain validation

Validated at 2026-10-16 15:26 CEST.

Direct imported commands from `/home/tritlo/Code/mcfta`:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-plain/domain-review-public.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-plain/domain-review-kernels.lean
```

Final direct exit codes: 0 and 0. Public checks: thirteen axiom reports and full signatures, plus Shape and Stored definition signatures. Integration checks: five kernels and their axiom reports. Neither final log contains a warning, error, or `sorryAx`. All reported axioms belong to `propext`, `Classical.choice`, and `Quot.sound`. `domain-review-results.json` records actual direct exit codes and report counts. The first kernel log retains the corrected local probe's free-variable `decide` error; no proof-module change was required.

Root-owned `domain-build-1.log` records canonical success in 1403 jobs. The reviewer ran no Lake, Haskell build, or Git action and changed no proof module or old evidence. Only new `domain-review*` and `region-next-review*` evidence was written. Source and text snapshot hashes match the frozen source. No owned process or build slot remains active.
