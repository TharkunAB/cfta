# Independent plain edge-call validation

Validated at 2026-10-16 15:32 CEST.

Direct imported commands from `/home/tritlo/Code/mcfta`:

```sh
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-plain/edgecall-review-public.lean
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-parent-plain/edgecall-review-kernels.lean
```

Both final direct processes returned exit code 0. The public run checks the complete explicit finite signature and its axioms. The kernel run proves four integration theorems and prints their axiom dependencies. Neither final log contains a warning, error, or `sorryAx`. Only `propext`, `Classical.choice`, and `Quot.sound` occur. `edgecall-review-results.json` records actual process exits and report counts. The first kernel log retains an unused probe typeclass warning; it was corrected only in the evidence source.

Root-owned `edgecall-build-1.log` records canonical success in 1500 jobs. Root-owned `audit-build-1.log` records aggregate success in 2485 jobs and 58868 theorem dependency checks. `Audit.lean:2036` imports this exact module. Root reported both canonical handles terminal exit 0. The only aggregate warning is the historical unused-input warning. The frozen source hash still matches the imported source snapshot.

The reviewer ran no Lake, Haskell build, or Git action and changed no proof source, root document, or prior frozen evidence. Only new `edgecall-review*` files were written. No compiled artifacts, owned processes, or build slot remain.
