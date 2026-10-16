# Actual outer checks composition validation

Frozen 2026-10-16 14:40 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedPartialChecksComposition.lean`.
SHA256: `fa33c0760d884e885268d6b7cf165e3589575090d88db8be4b54423c0b3525f6` (331 lines).

## API and proof

Seventeen public endpoints cover all sixteen actual PartialGraph constructors plus the machine-range conversion:

- node_hit, node_evaluate;
- empty, union, binder, ordinary;
- edge_hit, edge_evaluate, edge_body;
- rows_nil, rows_cons;
- descendants_run;
- children_contradiction, children_live;
- walk_nil, walk_cons;
- resident_ranges.

The edge_body endpoint accepts the actual EdgeBody and its reached PartialEdgeActual.Ranges. Other nonterminal endpoints accept only their actual child graphs and child Checks. resident_ranges converts ParentWorkerActual.ResidentRanges through LocalReductionActual.ranges_of_finite. It adds no semantic or final-state premise.

A private input projection permits Direct inversion without eliminating through finish/rebuild output expressions. Some existential intermediate states need physical alignment. A private StableRun equality proof realizes both supplied finite child graphs at componentwise maximum bounds and compares the exact literal successful outcomes. This uses the frozen WorkerCompletion theorem. It does not assume a new future body completion or general graph existence. No public semantic, physical, or completion premise is added.

## Checks

Root canonical build: terminal exit 0, 1480 jobs, session 57418, checks-build-1.log. Only the historical dependency warning remains. No canonical build was run by this subtask.

Final direct source command exits 0 with no warnings:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedPartialChecksComposition.lean
```

Raw draft logs checks-direct-1.log through checks-direct-4.log are retained. The final log is checks-direct-4.log. The earlier failures concern dependent elimination through computed result states, reflexive substitutions, and local binder names; no source definition or public premise was weakened to remove them.

Final imported direct commands both exit 0:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-outer-actual/checks-public.lean > lean/restart-evidence/20261016-outer-actual/checks-public-1.log 2>&1
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-outer-actual/checks-kernels.lean > lean/restart-evidence/20261016-outer-actual/checks-kernels-1.log 2>&1
```

All seventeen public axiom/full-signature checks pass. Foundations are limited to propext, Classical.choice, and Quot.sound. All six integration kernels pass with no warnings:

1. Evaluating an ordinary node with empty rows composes checks without a machine-range supplier.
2. The actual winning edge's resident range plan yields checks and call-level ranges at that same evaluation.
3. Inherited contradiction gives descendant checks without child requests.
4. One row composes a warm edge hit, the RETURNED edge's contradiction descendants, and the suffix.
5. A live indexed child branch composes its literal descended node hit and returned-state suffix.
6. Union and successful literal Mu leaves require no future edge-body plan.

Only the new proof and new checks-* evidence are written. Older proofs, Haskell, Audit, docs, and Git state are untouched. No compiled evidence artifact or active process remains. This is a structural soundness helper over supplied actual completed graphs; it is not general constrained completion or a GHC/runtime transfer.
