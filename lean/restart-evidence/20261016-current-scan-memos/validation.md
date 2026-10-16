# Current checked Scan memos and selected required execution

Verified on 2026-10-16. Source main is `8f85ddb6`.
The starting published proof checkpoint is `ca0b8697`.
Proof commits are `e715f34c`, `bc99fc26`, `2ce01ce2`, and `aad5d624`.
Ten new proof modules are frozen in `frozen-modules.json`.
No Haskell implementation or test file changed.

## Canonical checks

The pinned toolchain is Lean 4.34.1.
The full command is:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

The full Audit passes with 2337 jobs and 56426 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The preexisting unused-input warning remains.
The terminal log is `audit.log`.

Focused builds pass for native receipts (1120 jobs), current conjunction
receipts (1124), selected records and required execution (1277), query and
allocated Scan wrappers including seeded receipts (1330), required global
receipts (1284), and allocated required execution (1348).
All builds reached terminal success.
Earlier failed elaboration logs remain beside the successful logs.

## Direct probes and independent reviews

| Component | Public axiom reports | Public signatures | Integration kernels |
| --- | ---: | ---: | ---: |
| Native and seeded global receipts | 6 | 6 | 9 |
| Current conjunction receipts | 11 | 22 | 5 |
| Original selected records and required execution | 9 | 9 | 7 |
| Current query and allocated Scan wrappers | 4 | 6 | 3 |
| Required global and allocated required wrappers | 3 | 3 | 5 |
| Total | 33 | 46 | 29 |

All final direct probes pass. Eight named kernels also have separate axiom
reports and signatures. The reported axiom sets contain only the permitted
foundations. The component validation reports describe the exact kernels.
The independent source reviews found no material defect.
No proof source changed after its final successful build and freeze.

## Preservation

`verify-preservation.py` verifies all 3712 starting files remain.
All 2326 older non-Audit proof sources retain identical bytes.
All 14 frozen source manifests pass.
Stashes, other worktree records, and the root Haskell fix registry remain.
Only additive Audit imports and the seven restart documents differ among
the starting tracked files.
Earlier unavailable external drafts are not claimed recovered or reverified.
`preservation-final.json` records the complete check.

The unchanged Haskell source retains the earlier strict Nix build, 777
examples plus golden, five-file Fourmolu, and four-package Cabal-gild checks.
The root FINDINGS registry records failure cases, files, commits, validation,
and upstream status for the historical Haskell repairs.

## Scope

The constructed endpoint derives an actual checked Scan and, on its successful
branch, finite required-path preparation. It retains the original selected
record positions, exact current cache and operation state, and global memo
receipts. Initial legitimate memo invariants, allocation History, source
coverage, inherited readiness, and reached word ranges remain explicit.

The next boundary is the allocation-aware checked merge and shared target
state. The older class-edit graph uses a different native execution and
omits live equality operations. Its proofs remain useful component evidence.
`next-class-edit-boundary.md` gives exact source paths and next obligations.
The full class pass, final empty propagation, general constrained outer
caller, and other full-library obligations remain active.
This checkpoint does not establish whole-library Haskell correspondence.
