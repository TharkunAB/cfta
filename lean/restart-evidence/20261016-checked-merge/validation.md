# Checked allocated merge and selected target operands

Verified on 2026-10-16. Source main is `8f85ddb6`.
The starting published proof checkpoint is `b7510ec5`.
Proof commits are `784b2168`, `6938c72f`, and `4d9ea213`.
Five new proof modules are frozen in `frozen-modules.json`.
No Haskell implementation or test file changed.

## Canonical builds

The pinned toolchain is Lean 4.34.1.
The full command is:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.Audit
```

The full Audit passes with 2342 jobs and 56610 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The preexisting unused-input warning remains. `audit.log` is terminal green.

Focused canonical builds pass for Graph (1070 jobs), Physical (1099),
selected projection (1256), and checked merge plus operand (1272).
Each build reached terminal exit 0. Earlier failed direct and focused
elaboration logs remain beside the final successful logs.

## Public probes and integration kernels

| Component | Public axiom reports | Public signatures | Integration kernels |
| --- | ---: | ---: | ---: |
| Allocated graph and erasure | 12 | 12 | 9 |
| Dynamic physical invariants | 7 | 7 | 9 |
| Current selected projection | 3 | 4 | 4 |
| Checked merge and target operand | 8 | 12 | 4 |
| Total | 30 | 35 | 26 |

All final direct probes pass. Eight named kernels have additional axiom
reports and signatures. Only the permitted foundations occur.
The component reports describe the exact probes and their scope.
Independent source reviews found no material defect.
No proof source changed after its final canonical build and freeze.

The strongest checked integration constructs projection-plus-merge and the
next generated native query. The query derives its expanded inventory and
result law from its actual reached WordRanges. It takes no future result
law, generated model, or admission oracle. Other kernels check exact hits,
Top allocation, the empty-And predicate distinction, retained native tables,
open unrelated siblings, current required support, and ordered projections.

## Preservation

`verify-preservation.py` verifies all 3792 starting files remain.
All 2336 older non-Audit proof sources retain identical bytes.
All 15 frozen source manifests pass.
Stashes, other worktree records, and the root Haskell fix registry remain.
Only additive Audit imports and the seven restart documents differ among
the starting tracked files. Earlier unavailable external drafts are not
claimed recovered or reverified. `preservation-final.json` records the check.

The unchanged Haskell source retains the earlier strict Nix build, 777
examples plus golden, five-file Fourmolu, and four-package Cabal-gild checks.
Root FINDINGS records the historical Haskell repairs and upstream status.
The literal-clear distinction changes a proof adapter, not Haskell behavior.

## Remaining scope

Initial checked readiness, actual input inventory At, available selected
forest/domain, valid global tables, warm merge Stored, and uniform ambient
CacheCovers remain explicit premises. Empty merge tables derive the last
two invariants. There is no production global reset claim.

The graph is a completed sequential projection. Source selection's literal
noConstraint CAF allocation, host equality and identity correspondence,
HashMap iteration, lazy forcing, and pending publication remain adapters.
Final-row allocation alone does not prove those runtime traces.

`checked-target-fold-next.md` records the next constructive target fold,
class-local slots, force, leaf and class edits. Final empty propagation,
the general constrained outer caller, and broader full-library obligations
remain active. This checkpoint is progress, not whole-library completion.
