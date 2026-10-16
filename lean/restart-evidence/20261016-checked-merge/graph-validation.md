# Allocated merge graph validation

Validated 2026-10-16 08:42 CEST with pinned Lean v4.34.1.

Source: `MicroCFTA/SourceCurrentAllocatedMergeGraph.lean`, 292 lines.
SHA256: e48d2a8a3a42a44a58a472565b0b8fbfea2e09f66cf10e5bbd5325967b29b116.

The additive source defines concrete physical Code/Run/Call graphs. A Top-row instruction executes `emptyField` on the equality state and the original raw `makeEdge Top` on the constructor heap. Small raw instructions and completed hits do not add this equality operation. The map/column/group/body builders retain the old ordered code.

Public graph APIs:

- `erase_map`, `erase_retainedColumn`, `erase_small`, `erase_column`, `erase_large`, `erase_group`, `erase_root`, `erase_body`.
- `Run.graph`, `Call.graph`: exact old heap/result/merge-memo receipts.
- `run_lift code actual operations`, `call_lift actual operations`: constructive allocated graph from the actual old erased graph and arbitrary initial equality state. The lifts retain exact output, constructor heap, and merge memo. They supply the returned equality state rather than assume it. No validity or language conclusion is asserted by these lifts alone.

Focused canonical command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedMergeGraph
```

Result: terminal exit 0, 1070 jobs. No new warning. The old unused `inputs` warning from InternedFreshOrdinaryClosedCompletion was replayed.

Direct probes:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-merge/graph-public.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-merge/graph-kernels.lean
```

Both exit 0 with no warning. Exactly 12 public theorem axiom reports, 12 signatures, and 9 kernel compositions passed. All public theorems use only propext and Quot.sound. Kernels check the literal Top allocation, unchanged raw-work equality state, unchanged completed hit, EmptyNode miss, constructive old-call lifting/erasure, two ordered Top allocations, actual field availability and unchanged combination/descent tables, matching literal Top, and a raw empty-And distinction from the old plain predicate.

Earlier direct elaboration logs are retained. The dependent select/request inversion required private instruction-discriminator lemmas. No old source was changed. Source is frozen. Physical validity, completion, and checked-native wrappers are separate additive modules.
