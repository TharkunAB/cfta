# Current allocated merge integration validation

Validated at 2026-10-16 16:45 CEST.

The final independent direct check passed with terminal exit 0.
`merge-kernels-2.log` has no errors, warnings, or `sorryAx`.
All three named integration theorems have an axiom report and a signature check.
The failed first attempt is retained.
The checks import the canonical final module built by the parent with 1260 jobs.

## Integration checks

1. `cold_empty_then_warm` constructs an actual allocated Empty miss, its pure body, the literal remembered winner, and a subsequent actual hit. It applies `Merge.allocated` to both calls. Both complete physical states are the same as the input state. This includes the actual heap and equality-operation state. Physical and structural merge invariants are derived from the cold empty memo and retained for the warm hit.
2. `finite_then_finite_warm` invokes `Merge.finite` twice. The second invocation uses only the first call's derived physical readiness, stored invariants, and retained original availability. The actual first call supplies its stored winner. Case inversion of the second actual call proves that it must be a hit. The second output, full physical state, and full merge table equal the first returned ones. The stored owner is the exact original input.
3. `constrained_small_group` constructs a literal singleton-group body. It executes the ordered empty-child map, small-row constructor, group map, and final node constructor. The original complete field is retained. Its equality classes and residual guard remain arbitrary. The actual allocated miss is then checked by `Merge.allocated`. The equality-operation state remains exactly unchanged on this small branch.

## Scope review

No desired result domain, future producer law, successful body callback, or future-state invariant is supplied to these kernels.
`Ready` and warm-table physical and structural invariants remain explicit legitimate initial conditions.
The cold Empty kernel derives both warm-table invariants from empty tables.
The serial finite kernel derives the second call's conditions from the first actual return.
The small-group kernel uses exact raw constructors and actual source grouping.

These are domain-preservation and physical-state checks. They do not prove merge language equality or a height bound for merge results.
They use the current completed sequential allocated graph. They do not establish pending publication, host lazy demand, GHC evaluation order, or runtime correspondence.
The separate `merge-cache-kernels.lean` checks the losing reference candidate and earlier-winner rule; this file does not repeat that proof.

## Frozen sources

- `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMerge.lean`: `22fc4bccb3362795fb7032da17451d6df29ca3d4888958e6d37ffbdda95d3bbf`.
- `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryMergeCode.lean`: `eabab8ddf1f8037587afe47a919b6476113c73a18d6ee658c0ecff7b2eeed3ff`.

The pinned direct executable is `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean`.
`LEAN_PATH` is `/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean`.
This task changed only new `merge-kernels*` evidence files. It did not edit any proof source or run Lake, Git, or Haskell checks.
